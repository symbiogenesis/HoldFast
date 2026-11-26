# SPDX-License-Identifier: Apache-2.0
"""Validate tracked files against HoldFast's licensing policy."""

import glob
import re
import tomllib
from pathlib import Path, PurePosixPath

from toolchain import corpus

_MANIFEST = "REUSE.toml"
_CODE_LICENSE = "Apache-2.0"
_PROSE_LICENSE = "CC-BY-4.0"
_ICON_LICENSE = "MIT"
_ICON_FILE = "docs/index.html"
_SPDX_TAG = "SPDX-License-" + "Identifier"
_SNIPPET_START = "SPDX-Snippet" + "Begin"
_SNIPPET_END = "SPDX-Snippet" + "End"
_COMMENT_PREFIX = r"(?:[#;*]|//|/\*|\(\*|<!--)"
_DECLARATION = re.compile(
    rf"(?m)^[ \t]*(?:{_COMMENT_PREFIX}[ \t]*)?{_SPDX_TAG}:"
    r"[ \t]*(.*?)[ \t]*(?:\*/|\*\)|-->)?[ \t]*$",
)
_IGNORE_BLOCK = re.compile(
    rf"(?ms)^[ \t]*{_COMMENT_PREFIX}[ \t]*REUSE-IgnoreStart\b[^\n]*\n"
    rf".*?^[ \t]*{_COMMENT_PREFIX}[ \t]*REUSE-IgnoreEnd\b[^\n]*",
)
_OPENING_MARK_EXAMPLE = (
    "<!-- REUSE-IgnoreStart -->\n\n```text\n"
    f"# {_SPDX_TAG}: {_CODE_LICENSE}\n"
    "```\n\n<!-- REUSE-IgnoreEnd -->"
)
_HASH_NAMES = frozenset({".editorconfig", ".gitattributes", ".gitignore", _MANIFEST})
_NO_MARK_SUFFIXES = frozenset({".md", ".json", ".lock"})
_COMMENT_SYNTAX = {
    ".py": ("# {}",),
    ".toml": ("# {}",),
    ".yml": ("# {}",),
    ".yaml": ("# {}",),
    ".ml": ("(* {} *)",),
    ".mli": ("(* {} *)",),
    ".mll": ("(* {} *)",),
    ".v": ("(* {} *)",),
    ".mly": ("/* {} */",),
    ".c": ("/* {} */",),
    ".rs": ("// {}",),
    ".an": ("// {}",),
    ".scm": ("; {}",),
    ".css": ("/* {} */",),
    ".mjs": ("// {}",),
    ".js": ("// {}",),
    ".hf": ("/* {} */", "// {}"),
    ".html": ("<!-- {} -->",),
}


def _path_license(path: PurePosixPath) -> str:
    if path.suffix == ".md" or (path.parent == PurePosixPath("docs/evidence") and path.suffix == ".json"):
        return _PROSE_LICENSE
    return _CODE_LICENSE


def _declaration_findings(path: PurePosixPath, text: str) -> list[str]:
    """Check license declarations that can override the path annotation."""
    expected = _path_license(path)
    if _SPDX_TAG not in text:
        return []
    if path.as_posix() == _ICON_FILE:
        snippet = (text.find(_SNIPPET_START), text.find(_SNIPPET_END))
    else:
        snippet = (-1, -1)
    ignored = [match.span() for match in _IGNORE_BLOCK.finditer(text)] if "REUSE-IgnoreStart" in text else []
    problems: list[str] = []
    for match in _DECLARATION.finditer(text):
        offset = match.start()
        if any(start <= offset < end for start, end in ignored):
            continue
        license_id = _ICON_LICENSE if snippet[0] < offset < snippet[1] else expected
        actual = match.group(1)
        if actual != license_id:
            line = text.count("\n", 0, offset) + 1
            problems.append(f"{path}:{line}: expected {license_id} in SPDX declaration, found {actual!r}")
    return problems


def marks_findings(root: Path, loaded: corpus.Corpus) -> list[str]:
    """Check opening marks and any additional SPDX license declarations."""
    findings: list[str] = []
    policy = loaded.get("COPYRIGHT.md")
    if policy is None or _OPENING_MARK_EXAMPLE not in policy.raw:
        findings.append("COPYRIGHT.md: missing the canonical Apache-2.0 example in a REUSE ignore block")

    tag = f"{_SPDX_TAG}: {_CODE_LICENSE}"
    for rel in loaded.tracked:
        path = PurePosixPath(rel)
        if rel.startswith("LICENSES/"):
            continue
        formats = ("# {}",) if path.name in _HASH_NAMES else _COMMENT_SYNTAX.get(path.suffix)
        if formats is None and path.suffix not in _NO_MARK_SUFFIXES:
            findings.append(f"{rel}: file kind has no SPDX comment syntax ruling")
            continue
        doc = loaded.get(rel)
        try:
            text = doc.raw if doc is not None else (root / rel).read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as err:
            findings.append(f"{rel}: cannot read SPDX declarations: {err}")
            continue
        if formats is None:
            findings.extend(_declaration_findings(path, text))
            continue
        first, _, rest = text.partition("\n")
        if first.startswith("#!"):
            first = rest.partition("\n")[0]
        expected = tuple(style.format(tag) for style in formats)
        if first not in expected:
            findings.append(f"{rel}: expected opening mark {expected[0]!r}, found {first!r}")
        elif text.count(_SPDX_TAG) > 1:
            findings.extend(_declaration_findings(path, text))
    return findings


def _pattern(path: str) -> re.Pattern[str]:
    if any(char in path for char in "\\?[]") or any(
        part in {"", ".", ".."} or ("**" in part and part != "**") for part in path.split("/")
    ):
        raise ValueError(f"unsupported annotation path {path!r}")
    return re.compile(glob.translate(path, recursive=True, include_hidden=True, seps="/"))


def _annotations(root: Path) -> list[tuple[re.Pattern[str], str]]:
    data = tomllib.loads((root / _MANIFEST).read_text(encoding="utf-8"))
    tables = data.get("annotations")
    version = data.get("version")
    if type(version) is not int or version != 1 or not isinstance(tables, list) or not tables:
        raise ValueError("expected version 1 and at least one annotation table")
    rules: list[tuple[re.Pattern[str], str]] = []
    for number, table in enumerate(tables, 1):
        if not isinstance(table, dict) or table.get("precedence", "closest") != "closest":
            raise ValueError(f"annotation {number} must be a table with closest precedence")
        paths = table.get("path")
        paths = [paths] if isinstance(paths, str) else paths
        if not isinstance(paths, list) or not paths or not all(isinstance(path, str) for path in paths):
            raise ValueError(f"annotation {number} requires a path or a nonempty list of paths")
        notice = table.get("SPDX-FileCopyrightText")
        notices = [notice] if isinstance(notice, str) else notice
        if not isinstance(notices, list) or not notices or not all(
            isinstance(item, str) and item.strip() for item in notices
        ):
            raise ValueError(f"annotation {number} requires nonempty copyright text")
        license_id = table.get(_SPDX_TAG)
        if license_id not in (_CODE_LICENSE, _PROSE_LICENSE):
            raise ValueError(f"annotation {number} has unsupported SPDX license {license_id!r}")
        rules.extend((_pattern(path), license_id) for path in paths)
    return rules


def _octicon_findings(root: Path, mit_text: str) -> list[str]:
    try:
        html = (root / _ICON_FILE).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as err:
        return [f"{_ICON_FILE}: cannot read the MIT snippet: {err}"]
    before, _, snippet = html.partition(_SNIPPET_START)
    notice, close_comment, svg = snippet.partition("-->")
    svg, close_snippet, _ = svg.partition(f"<!-- {_SNIPPET_END} -->")
    if (
        html.count(_SNIPPET_START) != 1
        or html.count(_SNIPPET_END) != 1
        or not before.rstrip().endswith("<!--")
        or not close_comment
        or not close_snippet
        or re.fullmatch(r"\s*<svg\b[^>]*>.*</svg>\s*", svg, re.DOTALL) is None
    ):
        return [f"{_ICON_FILE}: expected SPDX snippet markers around the GitHub icon"]
    lines = [line.strip() for line in notice.splitlines()]
    if f"{_SPDX_TAG}: {_ICON_LICENSE}" not in lines:
        return [f"{_ICON_FILE}: the GitHub icon snippet requires an MIT identifier"]
    title, _, body = mit_text.partition("\n\n")
    copyright_line, _, terms = body.partition("\n\n")
    holder = copyright_line.removeprefix("Copyright (c) ")
    notice_tag = "SPDX-SnippetCopyrightText"
    if (
        title != "MIT License"
        or not copyright_line.startswith("Copyright (c) ")
        or not holder
        or f"{notice_tag}: {holder}" not in lines
        or not terms.strip()
        or " ".join(terms.split()) not in " ".join(notice.split())
    ):
        return [f"{_ICON_FILE}: inline MIT copyright and permission notice must match LICENSES/MIT.txt"]
    return []


def findings(root: Path, loaded: corpus.Corpus) -> list[str]:
    """Check path assignments, tracked license texts, and the inline MIT notice."""
    problems: list[str] = []
    if _MANIFEST not in loaded.indexed:
        return [f"{_MANIFEST}: the root license manifest must be tracked"]
    try:
        rules = _annotations(root)
    except (OSError, ValueError) as err:
        return [f"{_MANIFEST}: {err}"]

    licenses = {f"LICENSES/{ident}.txt" for ident in (_CODE_LICENSE, _PROSE_LICENSE, _ICON_LICENSE)}
    tracked = set(loaded.tracked)
    for rel in loaded.tracked:
        path = PurePosixPath(rel)
        if rel.startswith("LICENSES/"):
            if rel not in licenses:
                problems.append(f"{rel}: license text is outside the repository license policy")
            continue
        if path.name == _MANIFEST and rel != _MANIFEST:
            problems.append(f"{rel}: license annotations belong in the root {_MANIFEST}")
            continue
        expected = _path_license(path)
        actual = next((ident for pattern, ident in reversed(rules) if pattern.fullmatch(rel)), None)
        if actual is None:
            problems.append(f"{rel}: no copyright and license assignment in {_MANIFEST}")
        elif actual != expected:
            problems.append(f"{rel}: expected {expected} in {_MANIFEST}, found {actual}")

    texts: dict[str, str] = {}
    for rel in sorted(licenses):
        if rel not in loaded.indexed:
            problems.append(f"{rel}: required license text must be tracked")
            continue
        try:
            text = (root / rel).read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as err:
            problems.append(f"{rel}: cannot read license text: {err}")
            continue
        if text.strip():
            texts[rel] = text
        else:
            problems.append(f"{rel}: required license text is empty")
    if _ICON_FILE not in tracked:
        problems.append(f"{_ICON_FILE}: embedded MIT notice must be in a tracked file")
    elif "LICENSES/MIT.txt" in texts:
        problems.extend(_octicon_findings(root, texts["LICENSES/MIT.txt"]))
    return problems
