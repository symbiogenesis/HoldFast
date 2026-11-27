# SPDX-License-Identifier: Apache-2.0
"""Content-addressed Rocq `.vo` support cache and batched kernel checking."""

import json
import os
import re
import shutil
import subprocess
import tempfile
import weakref
from collections.abc import Callable, Sequence
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
from pathlib import Path

from filelock import FileLock

from toolchain import elaborate_types, proofenv, solver_ledger
from toolchain.hashing import file_sha256, sha256_bytes

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
    hashes: dict[str, str],
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
    try:
        for name in names:
            source_file = entry / name
            vo_name = f"{Path(name).stem}.vo"
            vo_file = entry / vo_name
            if not source_file.is_file() or not vo_file.is_file():
                return False
            if file_sha256(source_file) != hashes[name]:
                return False
            if file_sha256(vo_file) != vo_digests[vo_name]:
                return False
    except OSError:
        return False
    return True


def _copy_artifacts(source_dir: Path, target_dir: Path, names: Sequence[str]) -> None:
    for name in names:
        stem = Path(name).stem
        for artifact in (name, f"{stem}.vo", f"{stem}.vos", f"{stem}.glob"):
            src = source_dir / artifact
            if src.is_file():
                shutil.copyfile(src, target_dir / artifact)


_REQUIRE_RE = re.compile(
    r"\b(?:From\s+\S+\s+)?Require\s+(?:(?:Import|Export)\s+)?([^.;]+)\."
)


def _strip_coq_comments(text: str) -> str:
    """Remove Coq nested ``(* ... *)`` comments and string literals before scanning Require lines."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    in_string = False
    while i < n:
        if in_string:
            if text[i] == '"' and i + 1 < n and text[i + 1] == '"':
                i += 2
                continue
            if text[i] == '"':
                in_string = False
            i += 1
            continue
        if text[i:i + 2] == "(*":
            depth += 1
            i += 2
            continue
        if depth > 0:
            if text[i:i + 2] == "*)":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if text[i] == '"':
            in_string = True
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def _local_dependencies(
    names: Sequence[str],
    sources: dict[str, bytes],
    directory: Path,
) -> tuple[dict[str, tuple[str, ...]], dict[str, list[tuple[str, str]]]]:
    """Return ``(local_deps, external_vo_deps)`` per unit."""
    stem_to_name = {Path(name).stem: name for name in names}
    local_deps: dict[str, tuple[str, ...]] = {}
    external_deps: dict[str, list[tuple[str, str]]] = {}
    for name in names:
        text = _strip_coq_comments(sources[name].decode("utf-8", errors="replace"))
        seen_local: list[str] = []
        seen_ext: list[tuple[str, str]] = []
        seen_tokens: set[str] = set()
        for match in _REQUIRE_RE.finditer(text):
            for tok in match.group(1).split():
                if tok in seen_tokens:
                    continue
                seen_tokens.add(tok)
                target = stem_to_name.get(tok)
                if target is not None and target != name:
                    seen_local.append(target)
                elif target is None:
                    ext_vo = directory / f"{tok}.vo"
                    if ext_vo.is_file():
                        seen_ext.append((f"{tok}.vo", file_sha256(ext_vo)))
        local_deps[name] = tuple(seen_local)
        external_deps[name] = seen_ext
    return local_deps, external_deps


def _materialize_legacy_tuple(
    directory: Path,
    names: list[str],
    sources: dict[str, bytes],
    hashes: dict[str, str],
    active_compiler: list[str],
    active_compile: CompileFn,
    active_cache: Path,
    active_digest: str,
) -> None:
    identity = json.dumps(
        {
            "compiler_sha256": active_digest,
            "compiler_args": active_compiler[1:],
            "files": [[name, hashes[name]] for name in names],
        },
        separators=(",", ":"),
    )
    key = sha256_bytes(identity.encode("utf-8"))
    entry = active_cache / key
    try:
        if _cache_hit(entry, key, names, hashes):
            _copy_artifacts(entry, directory, names)
            return
    except OSError:
        pass
    with FileLock(active_cache / f"{key}.lock", timeout=600):
        if not _cache_hit(entry, key, names, hashes):
            shutil.rmtree(entry, ignore_errors=True)
            stage = Path(tempfile.mkdtemp(prefix=f"stage-{key}-", dir=active_cache))
            try:
                _compile_all(active_compiler, stage, sources, active_compile)
                vo_digests = {
                    f"{Path(name).stem}.vo": file_sha256(stage / f"{Path(name).stem}.vo")
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


def _compile_unit(compiler: list[str], stage: Path, name: str, compile_fn: CompileFn) -> None:
    compiled = compile_fn(compiler, stage, name)
    if compiled.returncode:
        detail = (compiled.stderr or compiled.stdout).strip()
        raise RuntimeError(f"Rocq compilation of {name} failed: {detail}")


def _materialize_unit(
    name: str,
    unit_key: str,
    source: bytes,
    source_hash: str,
    transitive_deps: tuple[str, ...],
    unit_entries: dict[str, Path],
    ext_vo_deps: list[tuple[str, str]],
    source_directory: Path,
    target_directory: Path,
    active_compiler: list[str],
    active_compile: CompileFn,
    active_cache: Path,
) -> None:
    entry = unit_entries[name]
    try:
        if _cache_hit(entry, unit_key, [name], {name: source_hash}):
            _copy_artifacts(entry, target_directory, [name])
            return
    except OSError:
        pass
    with FileLock(active_cache / f"{unit_key}.lock", timeout=600):
        if not _cache_hit(entry, unit_key, [name], {name: source_hash}):
            shutil.rmtree(entry, ignore_errors=True)
            stage = Path(tempfile.mkdtemp(prefix=f"stage-{unit_key}-", dir=active_cache))
            try:
                for dep in transitive_deps:
                    _copy_artifacts(unit_entries[dep], stage, [dep])
                for ext_vo, _ in ext_vo_deps:
                    src_vo = source_directory / ext_vo
                    if src_vo.is_file():
                        shutil.copyfile(src_vo, stage / ext_vo)
                (stage / name).write_bytes(source)
                _compile_unit(active_compiler, stage, name, active_compile)
                vo_name = f"{Path(name).stem}.vo"
                vo_digests = {vo_name: file_sha256(stage / vo_name)}
                (stage / "receipt.json").write_text(
                    json.dumps({"key": unit_key, "vo_sha256": vo_digests}, sort_keys=True),
                    encoding="utf-8",
                    newline="\n",
                )
                stage.replace(entry)
            except BaseException:
                shutil.rmtree(stage, ignore_errors=True)
                raise
        _copy_artifacts(entry, target_directory, [name])


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
    hashes = {name: sha256_bytes(source) for name, source in units}
    active_compiler = list(compiler) if compiler is not None else [*proofenv.rocq_command(), "-q"]
    solver_ledger.check_prover_flags(active_compiler)
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
    # Preserve single-entry tuple caching when a caller injects a custom compile_fn (e.g. mocked tests).
    if compile_fn is not None:
        _materialize_legacy_tuple(
            directory, names, sources, hashes, active_compiler, active_compile, active_cache, active_digest,
        )
        return hashes

    local_deps, ext_deps = _local_dependencies(names, sources, directory)
    unit_keys: dict[str, str] = {}
    unit_entries: dict[str, Path] = {}
    transitive: dict[str, tuple[str, ...]] = {}
    in_degree: dict[str, int] = {}
    dependents: dict[str, list[str]] = {name: [] for name in names}

    def compute_unit(name: str, visiting: set[str]) -> str:
        if name in unit_keys:
            return unit_keys[name]
        if name in visiting:
            raise RuntimeError(f"cyclic Rocq unit dependency involving {name}")
        visiting.add(name)
        dep_keys = [[dep, compute_unit(dep, visiting)] for dep in sorted(local_deps[name])]
        visiting.remove(name)
        trans: list[str] = []
        seen_trans: set[str] = set()
        for dep in local_deps[name]:
            for item in transitive[dep]:
                if item not in seen_trans:
                    seen_trans.add(item)
                    trans.append(item)
            if dep not in seen_trans:
                seen_trans.add(dep)
                trans.append(dep)
        transitive[name] = tuple(trans)
        identity = json.dumps(
            {
                "schema": 2,
                "compiler_sha256": active_digest,
                "compiler_args": active_compiler[1:],
                "unit": name,
                "source_sha256": hashes[name],
                "deps": dep_keys,
                "external_vo": [[ext, digest] for ext, digest in sorted(ext_deps[name])],
            },
            separators=(",", ":"),
        )
        unit_key = sha256_bytes(identity.encode("utf-8"))
        unit_keys[name] = unit_key
        unit_entries[name] = active_cache / unit_key
        return unit_key

    for name in names:
        compute_unit(name, set())
        in_degree[name] = len(local_deps[name])
        for dep in local_deps[name]:
            dependents[dep].append(name)

    if len(names) == 1:
        only = names[0]
        _materialize_unit(
            only, unit_keys[only], sources[only], hashes[only], transitive[only],
            unit_entries, ext_deps[only], directory, directory, active_compiler, active_compile, active_cache,
        )
        return hashes

    max_workers = min(os.process_cpu_count() or 1, len(names))
    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        pending: dict[Future[None], str] = {}
        for name in names:
            if in_degree[name] == 0:
                fut = pool.submit(
                    _materialize_unit,
                    name, unit_keys[name], sources[name], hashes[name], transitive[name],
                    unit_entries, ext_deps[name], directory, directory, active_compiler, active_compile, active_cache,
                )
                pending[fut] = name
        while pending:
            done, _ = wait(pending, return_when=FIRST_COMPLETED)
            for fut in done:
                finished = pending.pop(fut)
                fut.result()
                for child in dependents[finished]:
                    in_degree[child] -= 1
                    if in_degree[child] == 0:
                        cfut = pool.submit(
                            _materialize_unit,
                            child, unit_keys[child], sources[child], hashes[child], transitive[child],
                            unit_entries, ext_deps[child], directory, directory,
                            active_compiler, active_compile, active_cache,
                        )
                        pending[cfut] = child
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
    cmd = [*proofenv.rocqchk_command(), "-silent", *units]
    solver_ledger.check_prover_flags(cmd)
    result = subprocess.run(
        cmd,
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
