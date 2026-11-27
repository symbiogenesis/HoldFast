# SPDX-License-Identifier: Apache-2.0
"""Export pure diagnostics and format previews as bounded SARIF."""

import codecs
import copy
from collections.abc import Callable
from dataclasses import dataclass
from itertools import islice
from pathlib import Path
from typing import cast

from toolchain import MAX_SOURCE_BYTES
from toolchain.hashing import read_bounded, sha256_bytes
from toolchain.jsonutil import canonical_bytes, json_digest
from toolchain.lsp import diagnose
from toolchain.lsp_format import format_document, formatting_edits
from toolchain.lsp_services import InspectionError
from toolchain.protocol_json import decode_message
from toolchain.source import SourceSnapshot

SCHEMA_URI = "https://docs.oasis-open.org/sarif/sarif/v2.1.0/os/schemas/sarif-schema-2.1.0.json"
SCHEMA_SHA256 = "ad6db49878699b091f3eeb765b6e29e92a34bad4da88664d000c923b549c3a25"
MAX_SCHEMA_BYTES = 300_000
MAX_FILES = 16
MAX_REPORT_BYTES = 1_048_576
MAX_FINDINGS = 4096
SCOPE = "holdfast-pure-batch-diagnostics-v1"
KINDS = frozenset({"syntax", "name", "type", "encoding", "unsupported", "limit", "timeout", "internal"})
INCOMPLETE = frozenset({"unsupported", "limit", "timeout", "internal", "format-unavailable"})
RULE_IDS = tuple(sorted({f"HOLDFAST-{kind.upper()}" for kind in KINDS}
                        | {"HOLDFAST-FORMAT", "HOLDFAST-FORMAT-UNAVAILABLE"}))
type Object = dict[str, object]
type Checker = Callable[[bytes], Object | None]
type Formatter = Callable[[bytes], Object]


@dataclass(frozen=True)
class Input:
    """One explicit standalone compilation input; imports remain unsupported."""

    uri: str
    source: bytes

    def snapshot(self) -> SourceSnapshot:
        return SourceSnapshot(self.uri, 1, self.source.decode("utf-8"), 1)


def _inputs(inputs: tuple[Input, ...]) -> None:
    if not 1 <= len(inputs) <= MAX_FILES or len({item.uri for item in inputs}) != len(inputs):
        raise ValueError("SARIF requires 1 to 16 distinct source URIs")
    for item in inputs:
        if len(item.source) > MAX_SOURCE_BYTES:
            raise ValueError("SARIF source exceeds 65536 bytes")
        item.snapshot()


def _location(item: Input, index: int, line: int, column: int) -> Object:
    position = item.snapshot().diagnostic_position(line, column)
    return {"physicalLocation": {
        "artifactLocation": {"uri": item.uri, "index": index},
        "region": {"startLine": position["line"] + 1,
                   "startColumn": position["character"] + 1}}}


def _result(item: Input, index: int, rule: str, message: str, line: int, column: int) -> Object:
    return {"ruleId": rule, "ruleIndex": RULE_IDS.index(rule),
            "level": "warning" if rule == "HOLDFAST-FORMAT" else "error",
            "message": {"text": message}, "locations": [_location(item, index, line, column)]}


def _format_edits(item: Input, formatter: Formatter) -> list[Object]:
    formatted = formatter(item.source)
    edits = formatting_edits(item.snapshot(), formatted)
    if formatted.get("status") != "ok":
        raise InspectionError("requested canonical formatter did not finish")
    return edits


def export(inputs: tuple[Input, ...], producer: str, *, format_fixes: bool = False,
           checker: Checker = diagnose, formatter: Formatter = format_document) -> Object:
    """Project producer judgments without independently reimplementing analysis."""
    _inputs(inputs)
    if (not isinstance(producer, str) or len(producer) != 64
            or any(character not in "0123456789abcdef" for character in producer)):
        raise ValueError("SARIF producer must be a SHA-256 identity")
    results: list[Object] = []
    bindings: list[Object] = []
    notifications: list[Object] = []
    for index, item in enumerate(inputs):
        diagnostic = checker(item.source)
        status = "checked"
        if diagnostic is not None:
            kind = diagnostic.get("kind")
            if (set(diagnostic) != {"kind", "line", "column", "message"}
                    or not isinstance(kind, str) or kind not in KINDS
                    or type(diagnostic["line"]) is not int or type(diagnostic["column"]) is not int
                    or not isinstance(diagnostic["message"], str) or not diagnostic["message"]
                    or len(diagnostic["message"]) > 4096):
                raise ValueError("invalid diagnostic producer result")
            status = kind if kind in INCOMPLETE else "rejected"
            results.append(_result(item, index, f"HOLDFAST-{kind.upper()}",
                                   diagnostic["message"], diagnostic["line"], diagnostic["column"]))
        elif format_fixes:
            try:
                edits = _format_edits(item, formatter)
            except InspectionError:
                status = "format-unavailable"
                results.append(_result(item, index, "HOLDFAST-FORMAT-UNAVAILABLE",
                                       "Canonical formatter unavailable; requested analysis incomplete", 1, 1))
            else:
                if edits:
                    result = _result(item, index, "HOLDFAST-FORMAT",
                                     "Source differs from canonical HoldFast formatting", 1, 1)
                    result["fixes"] = [{
                        "description": {"text": "Preview canonical formatting of this exact source"},
                        "artifactChanges": [{"artifactLocation": {"uri": item.uri, "index": index},
                                             "replacements": [{
                                                 "deletedRegion": {"byteOffset": 0,
                                                                   "byteLength": len(item.source)},
                                                 "insertedContent": {"text": edits[0]["newText"]}}]}]}]
                    results.append(result)
        bindings.append({"uri": item.uri, "sha256": sha256_bytes(item.source), "status": status})
        if status in INCOMPLETE:
            notifications.append({"level": "error", "message": {
                "text": f"{item.uri}: {status}; no completed analysis verdict"}})
    complete = not notifications
    manifest: Object = {"schema": 1, "scope": SCOPE, "producer_sha256": producer,
                        "configuration": "pure-default-v1", "target": "gallina-pure-v1",
                        "schema_sha256": SCHEMA_SHA256, "format_fixes": format_fixes,
                        "complete": complete, "inputs": bindings,
                        "unqualified": True}
    document: Object = {"version": "2.1.0", "$schema": SCHEMA_URI, "runs": [{
        "tool": {"driver": {"name": "holdfast-pure-development", "semanticVersion": "0.0.0",
                              "rules": [{"id": rule, "shortDescription": {"text": rule}}
                                        for rule in RULE_IDS]}},
        "columnKind": "utf16CodeUnits", "artifacts": [
            {"location": {"uri": item.uri}, "length": len(item.source),
             "hashes": {"sha-256": sha256_bytes(item.source)}, "roles": ["analysisTarget"]}
            for item in inputs],
        "results": results, "invocations": [{"executionSuccessful": complete,
                                               "toolExecutionNotifications": notifications}],
        "properties": {"holdfast": manifest}}]}
    manifest["binding_sha256"] = json_digest(document)
    if len(results) > MAX_FINDINGS or len(canonical_bytes(document)) > MAX_REPORT_BYTES:
        raise ValueError("SARIF export exceeds report bounds")
    return document


def _schema_bytes(schema_path: Path) -> bytes:
    with schema_path.open("rb") as stream:
        raw = read_bounded(stream, MAX_SCHEMA_BYTES)
    if sha256_bytes(raw) != SCHEMA_SHA256:
        raise ValueError("SARIF schema does not match the pinned OASIS 2.1.0 bytes")
    return raw


def check_schema_current(schema_path: Path) -> None:
    """Recheck the exact external schema immediately before publication."""
    _schema_bytes(schema_path)


def schema_validator(schema_path: Path) -> Callable[[object], None]:
    """Load the offline schema and SARIF coordinate codec before sampling the producer."""
    from jsonschema import Draft4Validator  # noqa: PLC0415
    from referencing import Registry  # noqa: PLC0415

    codecs.lookup("utf-16-le")
    raw = _schema_bytes(schema_path)
    schema = decode_message(raw)
    Draft4Validator.check_schema(schema)
    validator = Draft4Validator(schema, registry=Registry())

    def check(document: object) -> None:
        errors = list(islice(validator.iter_errors(document), 8))
        if errors:
            raise ValueError("SARIF schema: " + "; ".join(error.message for error in errors[:8]))

    return check


def validate_schema(document: object, schema_path: Path) -> None:
    """Check one document against the pinned external schema."""
    schema_validator(schema_path)(document)


def validate(document: Object, inputs: tuple[Input, ...], producer: str,
             *, schema_path: Path | None = None) -> Object:
    """Refuse corrupt structure, coordinates, status and stale source/producer handoffs."""
    _inputs(inputs)
    if len(canonical_bytes(document)) > MAX_REPORT_BYTES:
        raise ValueError("SARIF report exceeds byte limit")
    if schema_path is not None:
        validate_schema(document, schema_path)
    try:
        if set(document) != {"version", "$schema", "runs"} or document["version"] != "2.1.0":
            raise ValueError("unexpected SARIF envelope")
        if document["$schema"] != SCHEMA_URI:
            raise ValueError("unexpected SARIF schema")
        runs = cast("list[Object]", document["runs"])
        if len(runs) != 1:
            raise ValueError("expected exactly one SARIF run")
        run = runs[0]
        manifest = cast("Object", cast("Object", run["properties"])["holdfast"])
        pending = copy.deepcopy(document)
        retained = cast("Object", cast("Object", cast("list[Object]", pending["runs"])[0]["properties"])["holdfast"])
        claimed = retained.pop("binding_sha256")
        if claimed != json_digest(pending):
            raise ValueError("SARIF report binding mismatch")
        bindings = cast("list[Object]", manifest["inputs"])
        if (type(manifest["schema"]) is not int or manifest["schema"] != 1 or manifest["scope"] != SCOPE
                or manifest["configuration"] != "pure-default-v1" or manifest["target"] != "gallina-pure-v1"
                or manifest["schema_sha256"] != SCHEMA_SHA256 or manifest["unqualified"] is not True
                or manifest["producer_sha256"] != producer or type(manifest["format_fixes"]) is not bool
                or len(bindings) != len(inputs)):
            raise ValueError("SARIF stale producer or invalid scope")
        artifacts = cast("list[Object]", run["artifacts"])
        if len(artifacts) != len(inputs) or run["columnKind"] != "utf16CodeUnits":
            raise ValueError("SARIF input or coordinate scope mismatch")
        rules = cast("list[Object]", cast("Object", cast("Object", run["tool"])["driver"])["rules"])
        if rules != [{"id": rule, "shortDescription": {"text": rule}} for rule in RULE_IDS]:
            raise ValueError("SARIF rule table mismatch")
        by_input: list[list[str]] = [[] for _ in inputs]
        results = cast("list[Object]", run["results"])
        if len(results) > MAX_FINDINGS:
            raise ValueError("SARIF finding limit")
        for result in results:
            rule = cast("str", result["ruleId"])
            if (rule not in RULE_IDS or type(result["ruleIndex"]) is not int
                    or result["ruleIndex"] != RULE_IDS.index(rule)):
                raise ValueError("SARIF unknown or inconsistent rule reference")
            message = cast("Object", result["message"])["text"]
            if not isinstance(message, str) or not message or len(message) > 4096:
                raise ValueError("SARIF invalid diagnostic message")
            locations = cast("list[Object]", result["locations"])
            if len(locations) != 1 or result["level"] != ("warning" if rule == "HOLDFAST-FORMAT" else "error"):
                raise ValueError("SARIF location or severity mismatch")
            physical = cast("Object", locations[0]["physicalLocation"])
            location = cast("Object", physical["artifactLocation"])
            index = location["index"]
            if type(index) is not int or not 0 <= index < len(inputs):
                raise ValueError("SARIF source index outside closure")
            item = inputs[index]
            if location["uri"] != item.uri:
                raise ValueError("SARIF source URI/index disagreement")
            region = cast("dict[str, int]", physical["region"])
            line, column = region["startLine"], region["startColumn"]
            if type(line) is not int or type(column) is not int or line < 1 or column < 1:
                raise ValueError("SARIF invalid source coordinate")
            snapshot = item.snapshot()
            offset = snapshot.position_byte_offset(line - 1, column - 1)
            if snapshot.byte_position(offset) != {"line": line - 1, "character": column - 1}:
                raise ValueError("SARIF coordinate exceeds source")
            if rule == "HOLDFAST-FORMAT":
                fixes = result.get("fixes")
                if not manifest["format_fixes"] or not isinstance(fixes, list) or len(fixes) != 1:
                    raise ValueError("SARIF format fix missing or unexpected")
                fix = cast("Object", fixes[0])
                changes = cast("list[Object]", fix["artifactChanges"])
                if len(changes) != 1 or changes[0]["artifactLocation"] != location:
                    raise ValueError("SARIF format fix source mismatch")
                replacements = cast("list[Object]", changes[0]["replacements"])
                if len(replacements) != 1 or canonical_bytes(replacements[0]["deletedRegion"]) != canonical_bytes({
                        "byteOffset": 0, "byteLength": len(item.source)}):
                    raise ValueError("SARIF format fix range mismatch")
                inserted = cast("Object", replacements[0]["insertedContent"])["text"]
                if not isinstance(inserted, str) or len(inserted.encode()) > MAX_SOURCE_BYTES:
                    raise ValueError("SARIF format fix exceeds source limit")
            elif "fixes" in result:
                raise ValueError("SARIF producer supplies no semantic fixes")
            by_input[index].append(rule)
        for index, (item, binding, artifact) in enumerate(zip(inputs, bindings, artifacts, strict=True)):
            status = binding["status"]
            if (binding["uri"] != item.uri or binding["sha256"] != sha256_bytes(item.source)
                    or canonical_bytes(artifact) != canonical_bytes({"location": {"uri": item.uri}, "length": len(item.source),
                                                      "hashes": {"sha-256": sha256_bytes(item.source)},
                                                      "roles": ["analysisTarget"]})):
                raise ValueError("SARIF stale input closure")
            expected = by_input[index]
            if status == "checked":
                valid = expected in ([], ["HOLDFAST-FORMAT"])
            elif status == "rejected":
                valid = len(expected) == 1 and expected[0] in {
                    "HOLDFAST-SYNTAX", "HOLDFAST-NAME", "HOLDFAST-TYPE", "HOLDFAST-ENCODING"}
            else:
                valid = status in INCOMPLETE and expected == [f"HOLDFAST-{cast('str', status).upper()}"]
            if not valid:
                raise ValueError("SARIF source status disagrees with findings")
        notifications = [{"level": "error", "message": {
            "text": f"{item['uri']}: {item['status']}; no completed analysis verdict"}}
            for item in bindings if item["status"] in INCOMPLETE]
        complete = not notifications
        if (manifest["complete"] is not complete
                or run["invocations"] != [{"executionSuccessful": complete,
                                           "toolExecutionNotifications": notifications}]):
            raise ValueError("SARIF completion status disagreement")
    except (KeyError, TypeError, IndexError, AttributeError) as error:
        raise ValueError("malformed HoldFast SARIF report") from error
    return manifest


def decode(raw: bytes) -> Object:
    """Decode bounded duplicate-free JSON before applying the handoff validator."""
    return decode_message(raw)


def encode(document: Object) -> bytes:
    """Bound the actual publication bytes as well as the normalized binding."""
    raw = canonical_bytes(document) + b"\n"
    if len(raw) > MAX_REPORT_BYTES:
        raise ValueError("SARIF publication exceeds byte limit")
    return raw
