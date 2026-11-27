# SPDX-License-Identifier: Apache-2.0
"""Content-addressed Rocq `.vo` support cache and batched kernel checking."""

import hashlib
import json
import shutil
import subprocess
import tempfile
import weakref
from collections.abc import Callable, Sequence
from pathlib import Path

from filelock import FileLock

from toolchain import elaborate_types, proofenv
from toolchain.hashing import file_sha256

type CompileFn = Callable[[list[str], Path, str], subprocess.CompletedProcess[str]]

_PRELUDE_UNIT = "HoldFastPrelude"
_PRELUDE_REQUIRES = (
    "From Corelib Require Init.Datatypes Init.Nat Init.Logic Init.Specif.\n"
    "From Stdlib Require Arith.PeanoNat Lia ZArith.BinInt.\n"
)
_PRELUDE_IMPORTS = (
    "Export HoldFastPrelude.\n"
    "Import Init.Datatypes Init.Nat Init.Logic Init.Specif Arith.PeanoNat Lia ZArith.BinInt.\n"
)

def support_cache_root() -> Path | None:
    """Return the persistent native Rocq `.vo` cache root, or `None` if unavailable."""
    cache = proofenv.build_root() / "rocq-support-cache"
    kind = proofenv.filesystem(cache)
    if not kind or kind in proofenv.CROSS_OS_FILESYSTEMS | proofenv.VOLATILE_FILESYSTEMS:
        return None
    return cache


def compiler_sha256(compiler: Sequence[str]) -> str | None:
    """Return a stat-memoized SHA-256 hex digest for ``compiler[0]``."""
    executable = shutil.which(compiler[0])
    if executable is None:
        return None
    path = Path(executable)
    if not path.is_file():
        return None
    try:
        return file_sha256(path)
    except OSError:
        return None


def _default_compile(compiler: list[str], directory: Path, name: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [*compiler, name],
        cwd=directory,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
        timeout=600,
    )


def _compile_all(
    compiler: list[str],
    directory: Path,
    sources: dict[str, bytes],
    compile_fn: CompileFn,
) -> None:
    for name, source in sources.items():
        (directory / name).write_bytes(source)
        compiled = compile_fn(compiler, directory, name)
        if compiled.returncode:
            detail = (compiled.stderr or compiled.stdout).strip()
            raise RuntimeError(f"Rocq compilation of {name} failed: {detail}")


def _cache_hit(
    entry: Path,
    key: str,
    names: Sequence[str],
    sources: dict[str, bytes],
) -> bool:
    receipt_path = entry / "receipt.json"
    if not receipt_path.is_file():
        return False
    try:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, ValueError):
        return False
    if not isinstance(receipt, dict) or receipt.get("key") != key:
        return False
    vo_digests = receipt.get("vo_sha256")
    if not isinstance(vo_digests, dict):
        return False
    expected_vo = {f"{Path(name).stem}.vo" for name in names}
    if set(vo_digests) != expected_vo:
        return False
    for name in names:
        source_file = entry / name
        vo_name = f"{Path(name).stem}.vo"
        vo_file = entry / vo_name
        if not source_file.is_file() or not vo_file.is_file():
            return False
        if source_file.read_bytes() != sources[name]:
            return False
        if hashlib.sha256(vo_file.read_bytes()).hexdigest() != vo_digests[vo_name]:
            return False
    return True


def _copy_artifacts(source_dir: Path, target_dir: Path, names: Sequence[str]) -> None:
    for name in names:
        stem = Path(name).stem
        for artifact in (name, f"{stem}.vo", f"{stem}.vos", f"{stem}.glob"):
            src = source_dir / artifact
            if src.is_file():
                shutil.copyfile(src, target_dir / artifact)


def materialize_units(
    directory: Path,
    units: Sequence[tuple[str, bytes]],
    *,
    compiler: Sequence[str] | None = None,
    cache_dir: Path | None = None,
    compiler_digest: str | None = None,
    compile_fn: CompileFn | None = None,
    use_default_cache: bool = True,
) -> dict[str, str]:
    """Compile or materialize cached `.v`/`.vo` artifacts into ``directory`` and return source SHA-256 hashes."""
    if not units:
        return {}
    names = [name for name, _ in units]
    sources = dict(units)
    hashes = {name: hashlib.sha256(source).hexdigest() for name, source in units}
    active_compiler = list(compiler) if compiler is not None else [*proofenv.rocq_command(), "-q"]
    active_compile = compile_fn if compile_fn is not None else _default_compile
    active_cache = cache_dir if cache_dir is not None else (support_cache_root() if use_default_cache else None)
    active_digest = (
        compiler_digest
        if compiler_digest is not None
        else (compiler_sha256(active_compiler) if active_cache is not None and use_default_cache else None)
    )
    if active_cache is None or active_digest is None:
        _compile_all(active_compiler, directory, sources, active_compile)
        return hashes
    active_cache.mkdir(parents=True, exist_ok=True)
    identity = json.dumps(
        {
            "compiler_sha256": active_digest,
            "compiler_args": active_compiler[1:],
            "files": [[name, hashes[name]] for name in names],
        },
        separators=(",", ":"),
    )
    key = hashlib.sha256(identity.encode("utf-8")).hexdigest()
    entry = active_cache / key
    with FileLock(active_cache / f"{key}.lock", timeout=600):
        if not _cache_hit(entry, key, names, sources):
            shutil.rmtree(entry, ignore_errors=True)
            stage = Path(tempfile.mkdtemp(prefix=f"stage-{key}-", dir=active_cache))
            try:
                _compile_all(active_compiler, stage, sources, active_compile)
                vo_digests = {
                    f"{Path(name).stem}.vo": hashlib.sha256((stage / f"{Path(name).stem}.vo").read_bytes()).hexdigest()
                    for name in names
                }
                (stage / "receipt.json").write_text(
                    json.dumps({"key": key, "vo_sha256": vo_digests}, sort_keys=True),
                    encoding="utf-8",
                    newline="\n",
                )
                stage.replace(entry)
            except BaseException:
                shutil.rmtree(stage, ignore_errors=True)
                raise
        _copy_artifacts(entry, directory, names)
    return hashes


def materialize_repo_units(
    root: Path,
    directory: Path,
    names: Sequence[str],
    *,
    compiler: Sequence[str] | None = None,
) -> dict[str, str]:
    """Materialize cached `.vo` artifacts for tracked files under ``tools/rocq/``."""
    units: list[tuple[str, bytes]] = []
    for raw_name in names:
        file_name = raw_name if raw_name.endswith(".v") else f"{raw_name}.v"
        units.append((file_name, (root / "tools" / "rocq" / file_name).read_bytes()))
    return materialize_units(directory, units, compiler=compiler)


def prelude_source() -> bytes:
    """Return compiled-module Gallina source for the shared HoldFast elaboration prelude."""
    return elaborate_types._PRELUDE.encode("utf-8")


def materialize_prelude(directory: Path, *, compiler: Sequence[str] | None = None) -> None:
    """Ensure cached ``HoldFastPrelude.vo`` artifacts are present in ``directory``."""
    materialize_units(directory, [(f"{_PRELUDE_UNIT}.v", prelude_source())], compiler=compiler)


def use_cached_prelude(
    gallina: str,
    directory: Path,
    *,
    compiler: Sequence[str] | None = None,
) -> tuple[str, bool]:
    """Replace an inline ``_PRELUDE`` in ``gallina`` with a cached ``HoldFastPrelude.vo`` import."""
    prelude = elaborate_types._PRELUDE
    idx = gallina.find(prelude)
    if idx == -1:
        return gallina, False
    mod_pos = gallina.rfind("\nModule ", 0, idx)
    if mod_pos != -1:
        insert_at = mod_pos + 1
    elif gallina.startswith("Module "):
        insert_at = 0
    else:
        return gallina, False
    materialize_prelude(directory, compiler=compiler)
    prefix = (
        gallina[:insert_at]
        + f"Require Import {_PRELUDE_UNIT}.\n"
        + _PRELUDE_REQUIRES
        + gallina[insert_at:idx]
    )
    suffix = gallina[idx + len(prelude):]
    return f"{prefix}{_PRELUDE_IMPORTS}{suffix}", True


def check_kernel(directory: Path, units: Sequence[str], *, timeout: int = 600) -> None:
    """Run ``rocqchk -silent`` over one or more compiled logical unit names."""
    if not units:
        raise ValueError("rocqchk requires at least one unit")
    result = subprocess.run(
        [*proofenv.rocqchk_command(), "-silent", *units],
        cwd=directory,
        capture_output=True,
        text=True,
        encoding="utf-8",
        check=False,
        timeout=timeout,
    )
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise RuntimeError(f"rocqchk failed for {' '.join(units)}: {detail}")


def _cleanup_tempdir(temp_dir: tempfile.TemporaryDirectory[str]) -> None:
    if Path(temp_dir.name).exists():
        temp_dir.cleanup()


class BatchChecker:
    """Accumulate compiled Rocq units in one working directory and run ``rocqchk`` once."""

    def __init__(self, prefix: str = "holdfast-rocq-batch-") -> None:
        self._prefix = prefix
        self._temp_dir: tempfile.TemporaryDirectory[str] | None = None
        self._finalizer: Callable[[], object] | None = None
        self._units: list[str] = []
        self._seen_units: set[str] = set()
        self._stem_counts: dict[str, int] = {}

    @property
    def work_dir(self) -> Path:
        if self._temp_dir is None:
            self._temp_dir = tempfile.TemporaryDirectory(prefix=self._prefix)
            self._finalizer = weakref.finalize(self, _cleanup_tempdir, self._temp_dir)
        return Path(self._temp_dir.name)

    @property
    def units(self) -> tuple[str, ...]:
        return tuple(self._units)

    def unique_stem(self, stem: str) -> str:
        """Return a collision-free unit filename stem within this batch directory."""
        count = self._stem_counts.get(stem, 0) + 1
        self._stem_counts[stem] = count
        return stem if count == 1 else f"{stem}_{count}"

    def register(self, unit: str) -> None:
        """Record a compiled unit name for batched ``rocqchk`` verification."""
        if unit not in self._seen_units:
            self._seen_units.add(unit)
            self._units.append(unit)

    def verify_all(self, *, timeout: int = 180) -> None:
        """Run ``rocqchk -silent`` once across all registered units and release temporary files."""
        try:
            if not self._units:
                raise RuntimeError("rocqchk batch has no registered units")
            check_kernel(self.work_dir, self._units, timeout=timeout)
        finally:
            self.close()

    def close(self) -> None:
        """Clean up the temporary batch directory if it was created."""
        if self._finalizer is not None:
            self._finalizer()
            self._finalizer = None
        self._temp_dir = None
