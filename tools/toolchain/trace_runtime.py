# SPDX-License-Identifier: Apache-2.0
"""Bounded Python installation file identities for compiler measurements."""

import hashlib
import json
import os
import stat
import sys
import sysconfig
from pathlib import Path

MAX_FILES = 20_000
MAX_BYTES = 512 * 1024 * 1024
_SUFFIXES = frozenset({".py", ".pyc", ".pyd", ".dll", ".so", ".zip"})


def _raise(error: OSError) -> None:
    raise error


def installation_files() -> dict[str, Path]:
    """Select stdlib, bytecode, extensions, archives and Python shared libraries.

    Third-party package trees and operating-system libraries are outside this
    inventory. Bytecode is included because imports can execute cached code.
    """
    standard = Path(sysconfig.get_path("stdlib"))
    if not standard.is_dir():
        raise ValueError("Python standard library is unavailable")
    roots = {"stdlib": standard}
    extension = sysconfig.get_config_var("DESTSHARED")
    if isinstance(extension, str) and extension:
        roots["extensions"] = Path(extension)
    if sys.platform == "win32":
        roots["extensions"] = Path(sys.base_prefix) / "DLLs"
    files: dict[str, Path] = {}

    def retain(label: str, path: Path) -> None:
        if len(files) >= MAX_FILES:
            raise ValueError("Python runtime inventory exceeds file limit")
        files[label] = path

    for label, root in roots.items():
        if not root.is_dir():
            raise ValueError("Python extension directory is unavailable")
        for directory, folders, names in root.walk(on_error=_raise):
            folders[:] = sorted(name for name in folders if name not in {"site-packages", "dist-packages"})
            for name in sorted(names):
                path = directory / name
                if path.is_symlink() and path.is_dir():
                    raise ValueError("Python runtime inventory cannot traverse directory aliases")
                if path.suffix in _SUFFIXES:
                    retain(f"{label}/{path.relative_to(root).as_posix()}", path)
    base = Path(sys.base_prefix)
    for directory in (base, base / "lib"):
        if directory.is_dir():
            for path in sorted(directory.iterdir()):
                if path.is_file() and path.suffix in {".dll", ".so", ".zip"}:
                    retain(f"installation/{path.relative_to(base).as_posix()}", path)
    library = (sysconfig.get_config_var("INSTSONAME") if sys.platform == "linux" else None)
    library = library or sysconfig.get_config_var("LDLIBRARY")
    libdir = sysconfig.get_config_var("LIBDIR")
    if sys.platform == "win32":
        libdir = str(base)
    if isinstance(library, str) and isinstance(libdir, str) and (
            library.endswith((".dll", ".so")) or ".so." in library):
        path = Path(libdir) / library
        if not path.is_file():
            raise ValueError("Python shared library is unavailable")
        retain("python-shared-library", path)
    if not files:
        raise ValueError("Python runtime inventory is empty")
    return files


def file_identity(files: dict[str, Path]) -> str:
    """Hash the declared inventory; missing, unreadable and oversized files refuse."""
    if not 0 < len(files) <= MAX_FILES:
        raise ValueError("runtime inventory exceeds file limit or is empty")
    inventory: dict[str, str] = {}
    digests: dict[Path, str] = {}
    size = 0
    for label, path in sorted(files.items()):
        if path in digests:
            inventory[label] = digests[path]
            continue
        digest = hashlib.sha256()
        if not stat.S_ISREG(path.stat().st_mode):
            raise ValueError("runtime inventory contains a nonregular file")
        with path.open("rb") as stream:
            before = os.fstat(stream.fileno())
            if not stat.S_ISREG(before.st_mode):
                raise ValueError("runtime inventory contains a nonregular file")
            while raw := stream.read(min(1024 * 1024, MAX_BYTES - size + 1)):
                size += len(raw)
                if size > MAX_BYTES:
                    raise ValueError("Python runtime inventory exceeds byte limit")
                digest.update(raw)
            after = path.stat()
            if not os.path.samestat(before, after) or (before.st_size, before.st_mtime_ns) != (
                    after.st_size, after.st_mtime_ns):
                raise ValueError("runtime file changed during observation")
        digests[path] = inventory[label] = digest.hexdigest()
    return hashlib.sha256(json.dumps(inventory, sort_keys=True, separators=(",", ":"),
                                     ensure_ascii=True).encode("ascii")).hexdigest()


def _linux_images(process: Path) -> dict[str, Path]:
    """Resolve the actual mapped files, including the loader and OCaml interpreter."""
    images: dict[str, Path] = {}
    with (process / "maps").open("rb") as stream:
        maps = stream.read(1024 * 1024 + 1)
    if len(maps) > 1024 * 1024:
        raise ValueError("process mappings exceed observation limit")
    for line in maps.splitlines():
        fields = line.split(None, 5)
        if len(fields) < 5:
            raise ValueError("malformed process memory map")
        if fields[4] == b"0":
            if b"x" in fields[1] and fields[-1] not in {b"[vdso]", b"[vsyscall]"}:
                raise ValueError("process executes an unbound anonymous mapping")
            continue
        if len(fields) != 6 or not fields[5].startswith(b"/") or fields[5].endswith(b" (deleted)"):
            raise ValueError("unavailable mapped runtime file")
        path = Path(os.fsdecode(fields[5]))
        info = path.stat()
        major, minor = fields[3].split(b":")
        if sys.platform == "linux" and (
                (os.major(info.st_dev), os.minor(info.st_dev), info.st_ino)
                != (int(major, 16), int(minor, 16), int(fields[4]))):
            raise ValueError("mapped runtime file was replaced")
        images[str(path)] = path
    if not images:
        raise ValueError("process has no observable file-backed images")
    return images


def _windows_images(pid: int) -> dict[str, Path]:
    if sys.platform != "win32":
        raise ValueError("Windows module observation requires Windows")
    import ctypes  # noqa: PLC0415
    from ctypes import wintypes  # noqa: PLC0415

    kernel = ctypes.WinDLL("kernel32", use_last_error=True)
    open_process = kernel.OpenProcess
    open_process.argtypes = (wintypes.DWORD, wintypes.BOOL, wintypes.DWORD)
    open_process.restype = wintypes.HANDLE
    close = kernel.CloseHandle
    close.argtypes = (wintypes.HANDLE,)
    enumerate_modules = kernel.K32EnumProcessModulesEx
    enumerate_modules.argtypes = (wintypes.HANDLE, ctypes.POINTER(wintypes.HMODULE),
                                  wintypes.DWORD, ctypes.POINTER(wintypes.DWORD), wintypes.DWORD)
    filename = kernel.K32GetModuleFileNameExW
    filename.argtypes = (wintypes.HANDLE, wintypes.HMODULE, wintypes.LPWSTR, wintypes.DWORD)
    modules = (wintypes.HMODULE * 1024)()
    needed = wintypes.DWORD()
    handle = open_process(0x0410, False, pid)  # PROCESS_QUERY_INFORMATION | PROCESS_VM_READ
    if not handle:
        raise ctypes.WinError(ctypes.get_last_error())
    try:
        if not enumerate_modules(handle, modules, ctypes.sizeof(modules), ctypes.byref(needed), 3):
            raise ctypes.WinError(ctypes.get_last_error())
        if not 0 < needed.value <= ctypes.sizeof(modules) or needed.value % ctypes.sizeof(wintypes.HMODULE):
            raise ValueError("process module inventory exceeds bound or is empty")
        images: dict[str, Path] = {}
        for module in modules[:needed.value // ctypes.sizeof(wintypes.HMODULE)]:
            name = ctypes.create_unicode_buffer(32768)
            length = filename(handle, module, name, len(name))
            if not 0 < length < len(name):
                raise ValueError("process module path could not be observed")
            path = Path(name.value)
            if not path.is_absolute():
                raise ValueError("process module path is relative")
            images[str(path)] = path
        return images
    finally:
        close(handle)


def process_images(pid: int) -> dict[str, Path]:
    if sys.platform == "win32":
        return _windows_images(pid)
    if sys.platform == "linux":
        return _linux_images(Path(f"/proc/{pid}"))
    raise ValueError("unsupported process observation platform")


def execution_files() -> dict[str, Path]:
    """Bind the active package trees, module source/caches, and native process images."""
    files = {f"image/{name}": path for name, path in process_images(os.getpid()).items()}
    for index, entry in enumerate(sys.path):
        path = Path(entry)
        if path.is_file():
            files[f"import-archive/{index}/{path}"] = path
        elif path.name in {"site-packages", "dist-packages"} and path.is_dir():
            for directory, _folders, names in path.walk(on_error=_raise):
                for name in names:
                    package_file = directory / name
                    if package_file.is_symlink() and package_file.is_dir():
                        raise ValueError("package tree contains a directory alias")
                    files[f"package/{index}/{package_file}"] = package_file
                    if len(files) > MAX_FILES:
                        raise ValueError("runtime inventory exceeds file limit")
    for name, module in sys.modules.copy().items():
        source = getattr(module, "__file__", None)
        if isinstance(source, str) and not source.startswith("<"):
            path = Path(source).absolute()
            files[f"module/{name}/{path}"] = path
            cached = getattr(module, "__cached__", None)
            if isinstance(cached, str) and Path(cached).is_file():
                files[f"bytecode/{name}"] = Path(cached)
    return files


def identity() -> str:
    return file_identity({**installation_files(), **execution_files()})
