# HoldFast

**HoldFast** is a programming language for writing low-level systems code and
mathematical proofs in the same file. Calls expose ownership transfer and
read, write, and initialization loans with `move`, `in`, `ref`, and `out`.
Functions state preconditions and postconditions with `requires` and
`ensures`. Named invariants can be opened for an update and must hold again
when the block exits.

HoldFast aims to make strong guarantees practical to use and maintain across
both systems and application code. Shared constructs keep their meaning across
execution profiles. A profile defines the permitted runtime behavior, the
assurance policy defines the required properties, and each result names the
representation its evidence actually covers. [Assurance policy](docs/extensions/assurance-profiles.md#scope-and-the-governing-rule)

The first release qualifies the exact packet executable and an independently
authored systems package. The hosted application profile has its own runtime,
foreign bindings and comparison against a host-native application.
[Release delivery](PLAN.md#holdfast-first-release-delivery)

Try the [interactive playground](https://symbiogenesis.github.io/HoldFast/) or
browse the [authored examples](examples/). The
[language reference](docs/language/reference.md) describes the surface syntax and
marks the boundaries between the development tools and the language design.

## Development tools

- The [pure compiler](docs/tooling/pure-prototype.md) checks `Nat` and `bool`
  programs through a Rocq-extracted parser and emits Gallina. The
  [language server](docs/tooling/lsp-prototype.md) provides editor feedback
  for that subset.
- The [Menhir parser](docs/tooling/parser.md) recognizes a wider surface. The
  [mathematical elaborator](docs/tooling/elaboration-prototype.md) checks
  supported constructs and emits Gallina for replay by
  [Rocq](https://rocq-prover.org/).
- The [packet validator walkthrough](docs/tooling/packet-walkthrough.md)
  runs the lowered C for valid and invalid packets and inspects the resulting
  buffer and returned view. The [first-slice contract](docs/language/first-release.md#first-slice-qualification)
  defines the evidence required for the production artifact.

<a id="commands"></a>

## Quick start

Run `python tools/run.py` on Windows or `python3 tools/run.py` on Linux
with the [required Python version](tools/pyproject.toml). The runner dispatches
guest-only commands to WSL on Windows.

```text
python tools/run.py holdfast --help
python tools/run.py holdfast-playground
python tools/run.py validate
```

See the [tool guide](tools/README.md) for commands and validation profiles.

The [documentation index](docs/README.md) links the language, tooling, and
assurance contracts. The [first-release contract](docs/language/first-release.md)
defines the supported endpoint, and [PLAN.md](PLAN.md) tracks progress toward it.
