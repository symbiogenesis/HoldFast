# SPDX-License-Identifier: Apache-2.0
"""Replay an importing client's effect check through a locked package upgrade."""

import json
import re
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory

from tests.harness import TOOLS, Case, ensure, raises
from tests.test_holdfast_packages import _write
from toolchain import elaborate, packages, parser, proofenv, solver_ledger
from toolchain.ast import HoldFastError

ROOT = TOOLS.parent
DIRECT = """module Transfer.API;
public bool Copy(ref u32 input, ref u32 destination)
    effects reads(input), writes(destination)
    ensures result == true
{
    destination = input;
    return true;
}
public bool ReadSpan(ref Span<byte> input) effects reads(input) => input.CanRead;
"""
HELPERS = """module Transfer.Helpers;
internal u32 Inspect(ref u32 value) => value;
internal Unit Store(ref u32 destination, u32 value) {
    destination = value;
    return;
}
internal bool InspectSpan(ref Span<byte> input) => input.CanRead;
"""
REFACTORED = """module Transfer.API;
import Transfer.Helpers as Local;
public bool Copy(ref u32 input, ref u32 destination)
    effects reads(input), writes(destination)
    ensures result == true
{
    let observed = Local.Inspect(ref input);
    Local.Store(ref destination, observed);
    return true;
}
public bool ReadSpan(ref Span<byte> input) effects reads(input) => Local.InspectSpan(ref input);
"""
CLIENT = """module Client;
import Transfer.API as API;
public bool Observe(ref u32 input, ref u32 output)
    effects reads(input), writes(output)
    => API.Copy(ref input, ref output);
public bool ObserveSpan(ref Span<byte> input) effects reads(input) => API.ReadSpan(ref input);
"""


def _replay_opaque(gallina: str) -> None:
    [provider] = re.findall(r"^Definition (\w+_Copy) :", gallina, re.MULTILINE)
    [client] = re.findall(r"^Definition (\w+_Observe) :", gallina, re.MULTILINE)
    [postcondition] = re.findall(r"^Definition (\w+_Copy_ensures_0)\b", gallina, re.MULTILINE)
    [span_post] = re.findall(r"^Definition (\w+_ObserveSpan_post_input) :", gallina, re.MULTILINE)
    [module] = re.findall(r"^Module (HoldFastPackage_\w+)\.$", gallina, re.MULTILINE)
    ensure(f"Opaque {provider}." in gallina, "the client could unfold its provider")
    ensure(not solver_ledger.ledger(gallina), "the package depended on a solver assumption")
    with TemporaryDirectory() as temporary:
        directory = Path(temporary)
        consumer = f"""
Example copied input output : {module}.{client} input output = true :=
  {module}.{postcondition} input output.
Print Assumptions copied.
Example span_preserved input : {module}.{span_post} input = input := eq_refl.
"""
        (directory / "Consumer.v").write_text(gallina + consumer, encoding="utf-8")
        for command in (["rocq", "c", "-q", "Consumer.v"], ["rocqchk", "-silent", "Consumer"]):
            result = subprocess.run(["opam", "exec", "--switch", proofenv.ROCQ_SWITCH, "--", *command],
                                    cwd=directory, capture_output=True, timeout=180, check=False)
            ensure(result.returncode == 0, f"kernel refused the opaque effect client: {result.stderr[-2000:]!r}")
            if command[0] == "rocq":
                ensure(b"Closed under the global context" in result.stdout,
                       f"the client postcondition has kernel assumptions: {result.stdout[-2000:]!r}")


def _locked_refactor() -> None:
    with TemporaryDirectory() as temporary:
        workspace = Path(temporary)
        provider = _write(workspace, "transfer", "v1", {}, "Transfer.API")
        consumer = _write(workspace, "client", "v1", {"transfer": "v1"}, "Client")
        manifest = provider / packages.MANIFEST
        manifest.write_text(manifest.read_text(encoding="utf-8").replace(
            '"Transfer.API" = "module.hf"', '"Transfer.API" = "module.hf"\n"Transfer.Helpers" = "Helpers.hf"'),
            encoding="utf-8")
        api, helpers, client = provider / "module.hf", provider / "Helpers.hf", consumer / "module.hf"
        for path, source in ((api, DIRECT), (helpers, HELPERS), (client, CLIENT)):
            path.write_text(source, encoding="utf-8")
        lock, output = workspace / "lock.json", workspace / "bundle.json"

        def relock() -> None:
            packages.lock_package(ROOT, workspace, "client", "v1", lock)

        def build() -> bytes:
            packages.build_package(ROOT, workspace, lock, output)
            return output.read_bytes()

        relock()
        initial = build()
        _replay_opaque(json.loads(initial)["modules"]["Client"])
        api.write_text(REFACTORED, encoding="utf-8")
        with raises(ValueError) as stale:
            build()
        ensure("stale package lock" in str(stale.exception) and output.read_bytes() == initial,
               "the private helper refactor reused the old lock or replaced its retained bundle")

        relock()
        refactored = build()
        ensure(json.loads(refactored)["lock_sha256"] != json.loads(initial)["lock_sha256"],
               "the refactored package bundle did not bind fresh inputs")
        _replay_opaque(json.loads(refactored)["modules"]["Client"])

        def refuse(source_module: str, message: str) -> None:
            relock()
            with raises(HoldFastError) as refused:
                build()
            ensure(f"module '{source_module}'" in refused.exception.message and message in refused.exception.message,
                   f"expected {message!r} from {source_module}: {refused.exception}")
            ensure(output.read_bytes() == refactored, "a refused package replaced the retained bundle")

        api.write_text(REFACTORED.replace("reads(input), writes(destination)", "writes(destination)"), encoding="utf-8")
        refuse("Transfer.API", "reads parameter 'input'")
        api.write_text(REFACTORED, encoding="utf-8")
        helpers.write_text(HELPERS.replace("=> value;", """{
    let saved = value;
    value = 0u32;
    value = saved;
    return saved;
}"""), encoding="utf-8")
        refuse("Transfer.API", "mutates parameter 'input'")

        api.write_text(REFACTORED.replace("reads(input), writes(destination)", "writes(input, destination)"),
                       encoding="utf-8")
        refuse("Client", "mutates parameter 'input'")
        client.write_text(CLIENT.replace("reads(input), writes(output)", "writes(input, output)"), encoding="utf-8")
        relock()
        _replay_opaque(json.loads(build())["modules"]["Client"])

        refactored = output.read_bytes()
        client.write_text("""module Client;
import Transfer.Helpers as Local;
public u32 Observe(ref u32 input) effects reads(input) => Local.Inspect(ref input);
""", encoding="utf-8")
        refuse("Client", "cannot access private declaration 'Local.Inspect'")


def _locked_named_effects() -> None:
    with TemporaryDirectory() as temporary:
        workspace = Path(temporary)
        provider = _write(workspace, "transfer", "v1", {}, "Transfer.API")
        consumer = _write(workspace, "client", "v1", {"transfer": "v1"}, "Client")
        manifest = provider / packages.MANIFEST
        manifest.write_text(manifest.read_text(encoding="utf-8").replace(
            '"Transfer.API" = "module.hf"', '"Transfer.API" = "module.hf"\n'
            '"Transfer.Left" = "Left.hf"\n"Transfer.Right" = "Right.hf"\n"Transfer.Helpers" = "Helpers.hf"'),
            encoding="utf-8")
        for name, value in (("Left", 1), ("Right", 2)):
            (provider / f"{name}.hf").write_text(
                f"module Transfer.{name};\npublic u32 Step() effects none => {value}u32;\n", encoding="utf-8")
        helpers = provider / "Helpers.hf"
        sources = """module Transfer.Helpers;
import Transfer.Left as Source;
internal u32 Leaf() effects calls(Source.Step) => Source.Step();
internal u32 Forward() => Leaf();
"""
        helpers.write_text(sources, encoding="utf-8")
        (provider / "module.hf").write_text("""module Transfer.API;
import Transfer.Left { Step as Allowed };
import Transfer.Helpers as Helpers;
public u32 Run() effects calls(Allowed) => Helpers.Forward();
""", encoding="utf-8")
        client = consumer / "module.hf"
        source = """module Client;
import Transfer.Left as Chosen;
import Transfer.API as API;
public u32 Run() effects calls(Chosen.Step) => API.Run();
"""
        client.write_text(source, encoding="utf-8")
        lock = workspace / "lock.json"

        def build() -> None:
            packages.lock_package(ROOT, workspace, "client", "v1", lock)
            packages.build_package(ROOT, workspace, lock, None)

        build()
        client.write_text(source.replace("Transfer.Left", "Transfer.Right"), encoding="utf-8")
        with raises(HoldFastError) as wrong_target:
            build()
        ensure("module 'Client': callable transitively invokes 'Step'" in wrong_target.exception.message,
               f"a same-spelled callable from another module covered the bound: {wrong_target.exception}")

        client.write_text(source, encoding="utf-8")
        for unresolved in (
            "internal u32 Indirect(Fn(u32 value) -> u32 callback) => callback(3u32);\n",
            "internal Nat Recur(Nat n) decreases n => match (n) { 0 => 0, Succ(k) => Recur(k), };\n",
        ):
            helpers.write_text(sources + unresolved, encoding="utf-8")
            with raises(HoldFastError) as missing:
                build()
            ensure("recursive or indirect call needs explicit effects" in missing.exception.message,
                   f"the call missed the closed inference boundary: {missing.exception}")

        initializer = """internal Unit Initialize(out u32 output) effects writes(output) {
    output = 9u32;
    return;
}
"""
        call = """public Unit Fill(out u32 output) effects writes(output) {
    Helpers.Initialize(out output);
    return;
}
"""
        api = provider / "module.hf"
        api.write_text(api.read_text(encoding="utf-8") + call, encoding="utf-8")
        helpers.write_text(sources + initializer, encoding="utf-8")
        build()
        helpers.write_text(sources + initializer.replace("effects writes(output)", "effects none"), encoding="utf-8")
        with raises(HoldFastError) as missing_write:
            build()
        ensure("module 'Transfer.Helpers': callable mutates parameter 'output'" in missing_write.exception.message,
               f"an initializer passed with an empty write bound: {missing_write.exception}")


def _record_method_effect_targets() -> None:
    fields = b"""module FieldEffects;
public record Runner(Fn(u32 value) -> u32 Apply) {
    public u32 Run() effects reads(this), calls(Apply) => Apply(0u32);
    public u32 Forward() effects reads(this), calls(Apply) => this.Run();
}
"""
    parameters = b"""module ParameterEffects;
public record Runner(u32 Value) {
    public u32 Run(u32 seed, Fn(u32 value) -> u32 callback) effects calls(callback) => callback(seed);
}
public u32 Forward(Runner runner, Fn(u32 value) -> u32 action) effects calls(action) => runner.Run(0u32, action);
"""
    with parser.cached_build(ROOT) as compiled:
        def check(source: bytes) -> None:
            elaborate.elaborate(source, parser.parse_source(compiled, source, surface=True))

        check(fields)
        with raises(HoldFastError) as field:
            check(fields + b"public u32 Invoke(Runner runner) effects none => runner.Run();\n")
        ensure("transitively invokes 'Apply'" in field.exception.message,
               f"a projected callable missed its effect diagnostic: {field.exception}")

        check(parameters)
        with raises(HoldFastError) as parameter:
            check(parameters.replace(b"calls(action)", b"none"))
        ensure("transitively invokes 'action'" in parameter.exception.message,
               f"the record method's callback effect missed the actual argument: {parameter.exception}")

        with raises(HoldFastError) as partial:
            check(parameters + b"""
public definition Fn(Fn(u32 value) -> u32 callback) -> u32 Partial(Runner runner)
    effects none => runner.Run(0u32);
""")
        ensure("partial application" in partial.exception.message,
               f"an unapplied method callback missed the closed signature refusal: {partial.exception}")


def cases() -> list[Case]:
    return [Case("locked internal effect refactor preserves an opaque importing proof", _locked_refactor,
                 lane="toolchain"),
            Case("locked named effects follow resolved callable identities across aliases", _locked_named_effects,
                 lane="toolchain"),
            Case("record methods resolve callable field and argument effects", _record_method_effect_targets,
                 lane="toolchain")]
