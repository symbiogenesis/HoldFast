# SPDX-License-Identifier: Apache-2.0
"""Independent runtime inventory, cache freshness and bounded refusal controls."""

import hashlib
import io
import json
import os
import sys
import tempfile
from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from unittest.mock import patch

from tests.harness import Case, ensure
from toolchain import hashing
from toolchain import trace_runtime as runtime

INDEPENDENT_CASES = True


def _installation_inventory() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-runtime-inventory-") as temporary:
        base = Path(temporary)
        standard, extensions = base / "stdlib", base / "extensions"
        contents = {
            "stdlib/json/__init__.py": b"source",
            "stdlib/json/__pycache__/__init__.cpython-314.pyc": b"cached bytecode",
            "stdlib/site-packages/unrelated.py": b"third party",
            "stdlib/dist-packages/unrelated.py": b"third party",
            "stdlib/README.txt": b"documentation",
            "extensions/_json.so": b"extension",
            "lib/libpython3.14.so": b"shared Python",
            "lib/python314.zip": b"archived library",
        }
        for name, value in contents.items():
            path = base / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(value)
        variables = {"DESTSHARED": str(extensions), "LDLIBRARY": "libpython3.14.so",
                     "LIBDIR": str(base / "lib")}
        with patch.object(runtime, "execution_files", return_value={}), \
                patch.object(runtime.sys, "platform", "linux"), \
                patch.object(runtime.sys, "base_prefix", str(base)), \
                patch.object(runtime.sysconfig, "get_path", return_value=str(standard)), \
                patch.object(runtime.sysconfig, "get_config_var", side_effect=variables.get):
            selected = runtime.installation_files()
            ensure({label: path.relative_to(base).as_posix() for label, path in selected.items()} == {
                "stdlib/json/__init__.py": "stdlib/json/__init__.py",
                "stdlib/json/__pycache__/__init__.cpython-314.pyc": "stdlib/json/__pycache__/__init__.cpython-314.pyc",
                "extensions/_json.so": "extensions/_json.so",
                "installation/lib/libpython3.14.so": "lib/libpython3.14.so",
                "installation/lib/python314.zip": "lib/python314.zip",
                "python-shared-library": "lib/libpython3.14.so",
            }, "runtime inventory differs from independently chosen files")
            expected = {label: hashlib.sha256(path.read_bytes()).hexdigest()
                        for label, path in selected.items()}
            ensure(runtime.identity() == hashlib.sha256(json.dumps(
                expected, sort_keys=True, separators=(",", ":")).encode("ascii")).hexdigest(),
                "runtime identity differs from independent manifest digest")
            previous = runtime.identity()
            for name in ("stdlib/json/__init__.py", "stdlib/json/__pycache__/__init__.cpython-314.pyc",
                         "extensions/_json.so", "lib/libpython3.14.so", "lib/python314.zip"):
                (base / name).write_bytes(b"changed runtime file")
                current = runtime.identity()
                ensure(current != previous, f"runtime identity ignores {name}")
                previous = current
            added = standard / "new.py"
            added.write_bytes(b"new import")
            ensure(runtime.identity() != previous, "new runtime file retained identity")
            added.unlink()
            ensure(runtime.identity() == previous, "runtime deletion did not restore inventory")
            with patch.object(runtime, "MAX_FILES", 1):
                _refuses(runtime.installation_files)
            with patch.object(runtime, "MAX_BYTES", 1):
                _refuses(runtime.identity)
            (base / "lib/libpython3.14.so").unlink()
            _refuses(runtime.installation_files)


def _refuses(action: Callable[[], object]) -> None:
    try:
        action()
    except (OSError, ValueError):
        return
    raise AssertionError("unavailable or oversized Python runtime was accepted")


def _windows_inventory() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-runtime-windows-") as temporary:
        base = Path(temporary)
        for name in ("Lib/json.py", "DLLs/_json.pyd", "python314.dll", "vcruntime140.dll", "python314.zip"):
            path = base / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"Windows runtime")
        variables = {"LDLIBRARY": "python314.dll", "LIBDIR": str(base / "libs")}
        with patch.object(runtime.sys, "platform", "win32"), \
                patch.object(runtime.sys, "base_prefix", str(base)), \
                patch.object(runtime.sysconfig, "get_path", return_value=str(base / "Lib")), \
                patch.object(runtime.sysconfig, "get_config_var", side_effect=variables.get):
            ensure(set(runtime.installation_files()) == {
                "stdlib/json.py", "extensions/_json.pyd", "installation/python314.dll",
                "installation/vcruntime140.dll", "installation/python314.zip", "python-shared-library",
            }, "Windows extension, archive or shared runtime omitted")
            (base / "DLLs/_json.pyd").unlink()
            (base / "DLLs").rmdir()
            _refuses(runtime.installation_files)


def _linux_soname() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-runtime-soname-") as temporary:
        root = Path(temporary)
        shared = root / "libpython3.14.so.1.0"
        shared.write_bytes(b"installed runtime")
        variables = {"INSTSONAME": shared.name, "LDLIBRARY": "libpython3.14.so", "LIBDIR": str(root)}
        with patch.object(runtime.sys, "platform", "linux"), \
                patch.object(runtime.sys, "base_prefix", str(root)), \
                patch.object(runtime.sysconfig, "get_path", return_value=str(root)), \
                patch.object(runtime.sysconfig, "get_config_var", side_effect=variables.get):
            ensure(runtime.installation_files()["python-shared-library"] == shared,
                   "installed versioned library needs no development symlink")
            shared.unlink()
            (root / "libpython3.14.so").write_bytes(b"unrelated link-time library")
            _refuses(runtime.installation_files)


def _execution_closure() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-runtime-closure-") as temporary:
        root = Path(temporary)
        packages = root / "site-packages"
        packages.mkdir()
        native = root / "native"
        package_data = packages / "table.dat"
        settings = packages / "hooks.pth"
        code = root / "imported.py"
        cache = root / "imported.pyc"
        archive = root / "python.zip"
        expected = {native, package_data, settings, code, cache, archive}
        for path in expected:
            path.write_bytes(path.name.encode())
        module = ModuleType("test_module")
        module.__file__ = str(code)
        module.__dict__["__cached__"] = str(cache)
        with patch.object(runtime.sys, "path", [str(packages), str(archive)]), \
                patch.object(runtime.sys, "modules", {"test_module": module}), \
                patch.object(runtime, "process_images", return_value={"native": native}):
            ensure(set(runtime.execution_files().values()) == expected,
                   "package data, startup hook, import cache, archive or native image missing")
            identity = runtime.file_identity(runtime.execution_files())
            for path in expected:
                path.write_bytes(b"replacement")
                changed = runtime.file_identity(runtime.execution_files())
                ensure(changed != identity, f"changed {path.name} retained the running closure")
                identity = changed


def _process_images() -> None:
    actual = set(runtime.process_images(os.getpid()).values())
    ensure(any(path.is_file() and "python" in path.name.lower() for path in actual)
           and len(actual) > 1, "actual process image or transitive system libraries missing")
    with tempfile.TemporaryDirectory(prefix="holdfast-runtime-map-") as temporary:
        root = Path(temporary)
        library = root / "library with spaces.so"
        library.write_bytes(b"mapped")
        info = library.stat()
        device = f"{os.major(info.st_dev):x}:{os.minor(info.st_dev):x}" if sys.platform == "linux" else "00:01"
        record = f"1-2 r-xp 0000 {device} {info.st_ino} {library}\n"
        if sys.platform == "linux":
            (root / "maps").write_text(record + record, encoding="utf-8")
            ensure(set(runtime._linux_images(root).values()) == {library}, "mapped identity reconstruction")
            (root / "maps").write_text(record + record.replace(f" {info.st_ino} ", " 1 "), encoding="utf-8")
            _refuses(lambda: runtime._linux_images(root))
        for row in ("1-2 rwxp 0000 00:00 0\n", "1-2 r-xp 0000 00:01 2345 /old.so (deleted)\n"):
            (root / "maps").write_text(row, encoding="utf-8")
            _refuses(lambda: runtime._linux_images(root))


def _unavailable_inputs() -> None:
    with tempfile.TemporaryDirectory(prefix="holdfast-runtime-missing-") as temporary:
        missing = Path(temporary) / "missing.py"
        with patch.object(runtime, "installation_files", return_value={"missing": missing}), \
                patch.object(runtime, "execution_files", return_value={}):
            _refuses(runtime.identity)
        with patch.object(runtime.sysconfig, "get_path", return_value=str(missing)):
            _refuses(runtime.installation_files)


def _bounded_read_and_stat_memo_freshness() -> None:
    payload = b"0123456789" * 10
    ensure(hashing.read_bounded(io.BytesIO(payload), 100, chunk_size=7) == payload,
           "read_bounded truncated an in-bound stream")
    oversized = hashing.read_bounded(io.BytesIO(payload + b"extra"), 100, chunk_size=7)
    ensure(len(oversized) == 101 and oversized == payload + b"e",
           "read_bounded did not stop cleanly at limit + 1")

    with tempfile.TemporaryDirectory(prefix="holdfast-hashing-freshness-") as temporary:
        target = Path(temporary) / "sample.bin"
        target.write_bytes(b"aaaa")
        first = hashing.file_sha256(target)
        # Immediate same-size write within the racily-clean guard must not hit cache.
        target.write_bytes(b"bbbb")
        second = hashing.file_sha256(target)
        ensure(first != second and second == hashlib.sha256(b"bbbb").hexdigest(),
               "same-size immediate write returned a stale cached digest")
        past_ns = max(target.stat().st_mtime_ns, target.stat().st_ctime_ns) + hashing.RACILY_CLEAN_NS + 5_000_000_000
        with patch.object(hashing.time, "time_ns", return_value=past_ns):
            third = hashing.file_sha256(target)
            ensure(third == second, "aged file changed digest on cache population")
            ensure(hashing.cached_file_digest(target) == (third, 4),
                   "aged unchanged file missed the racily-clean cache")
        target.write_bytes(b"cccc")
        ensure(hashing.file_sha256(target) == hashlib.sha256(b"cccc").hexdigest(),
               "rewritten file retained stale cached digest")


def cases() -> list[Case]:
    return [Case("stdlib-cache-extension-and-shared-library-freshness", _installation_inventory),
            Case("bind-installed-linux-library-without-development-symlink", _linux_soname),
            Case("complete-running-package-code-cache-and-library-bytes", _execution_closure),
            Case("live-image-selection-and-stale-or-anonymous-mappings", _process_images),
            Case("windows-runtime-selection", _windows_inventory),
            Case("missing-runtime-inputs-refuse", _unavailable_inputs),
            Case("bounded-read-and-racily-clean-digest-cache", _bounded_read_and_stat_memo_freshness)]
