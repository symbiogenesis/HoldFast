# HoldFast Tools

Run `python tools/run.py` on Windows and `python3 tools/run.py` on Linux. The
runner dispatches guest-only commands to WSL on Windows. Run the runner with
`--help` to list commands, or append `--help` to a command to see its options.

## Commands

| Command | Lane | Purpose |
| --- | --- | --- |
| `python tools/run.py validate` | host / guest | Run the static gate and behavioral suite sequentially with bounded worker concurrency |
| `python tools/run.py validate --full` | host + guest | Run the complete local development qualification profile with native prerequisites required |
| `python tools/run.py validate --static` | host / guest | Run Python and Markdown checks |
| `python tools/run.py gate` | host / guest | Run `check`, `markdown`, and `typecheck` in one verdict |
| `python tools/run.py check` | host / guest | Check [licensing](../COPYRIGHT.md#file-markings), encoding and whitespace, source-comment links, pure source and Markdown examples, JavaScript and editor assets, and plan-summary arithmetic |
| `python tools/run.py check --fix` | host / guest | Refresh only the generated estimate table in [PLAN.md](../PLAN.md#current-summary), then run all `check` rules |
| `python tools/run.py markdown` | host / guest | Validate `tools/rumdl.toml` and run closed-world `rumdl` Markdown linting across the corpus |
| `python tools/run.py typecheck` | host / guest | Typecheck and lint `tools/` under pinned `ty` (`linux` + `win32`) and `ruff` |
| `python tools/run.py prepare python --path FILE` | host / guest | Order imports in the selected Python files under `tools/` with locked `ruff` |
| `python tools/run.py prepare markdown --path FILE` | host / guest | Format the selected `.md` files with locked `rumdl` |
| `python tools/run.py test` | host / guest | Run the `test_*.py` behavioral test suite |
| `python tools/run.py holdfast` | host | Pure HoldFast prototype checker, formatter, linter, Gallina emitter, and generated-test runner |
| `python tools/run.py holdfast-borrow-compare` | host / guest | Replay pinned Rust decisions and execute accepted observations for the [borrowing comparison](../docs/language/loan-analysis.md#conditional-borrowing-comparison) |
| `python tools/run.py holdfast sarif` | host | Export source-bound pure batch diagnostics and optional format previews as [SARIF 2.1.0](../docs/tooling/tooling-protocols.md#qualified-pure-batch-sarif), with an explicit external schema |
| `python tools/run.py holdfast-lsp` | host / guest | Serve pure HoldFast editor features over stdio, with optional wire-transcript recording |
| `python tools/run.py holdfast-lsp --qualify-clients` | host / guest | Check [editor interoperability](../docs/tooling/lsp-prototype.md#acceptance-and-remaining-qualification) with pinned Neovim and Vim clients |
| `python tools/run.py holdfast-lsp --qualify-rename` | Ubuntu ARM64 / WSL | Check versioned rename application and stale refusal in pinned Neovim and Emacs Eglot with [retained editor and wire evidence](../docs/tooling/lsp-prototype.md#local-rename-previews) |
| `python tools/run.py holdfast-lsp --qualify-actions` | Ubuntu ARM64 / WSL | Check [versioned Boolean comparison action application and stale refusal](../docs/tooling/authoring-tools.md#checked-boolean-comparison-previews) in pinned Neovim and Emacs Eglot |
| `python tools/run.py holdfast-highlight` | host / guest | Check/regenerate syntax-only editor assets; qualify pinned Tree-sitter and TextMate consumers in the guest |
| `python tools/run.py holdfast-playground` | guest (`[wsl]`) | Unified HoldFast browser playground with dependent mathematics |
| `python tools/run.py holdfast-parser` | guest (`[wsl]`) | Menhir parser build/qualification, syntax campaigns, dependent elaboration, first-slice harness, and Rocq kernel replay |
| `python tools/run.py holdfast-parser parse SOURCE [--surface]` | guest | Emit the development parser's [located JSON syntax](../docs/tooling/parser.md#acceptance-and-commands) using the pure grammar by default or the wider grammar with `--surface` |
| `python tools/run.py holdfast-parser fmt FILE --check` | guest | Check [canonical mathematical layout](../docs/tooling/authoring-tools.md#formatting-and-linting-mathematical-source). Omit `--check` to apply the checked formatting. |
| `python tools/run.py holdfast-parser fmt FILE --syntax-only` | guest | Apply canonical mathematical layout during semantic or proof repair. Add `--check` to leave the source untouched. |
| `python tools/run.py holdfast-parser fmt - --syntax-only` | guest | Read a UTF-8 editor buffer from standard input and return its canonical layout on standard output. |
| `python tools/run.py holdfast-parser lint FILE` | guest | Inspect mathematical source for declaration, binding, documentation, pattern, expression and contract warnings |
| `python tools/run.py holdfast-parser lock-package WORKSPACE NAME REVISION --output LOCK` | guest | Resolve and bind the explicit local dependency closure for the [mathematical batch target](../docs/tooling/elaboration-prototype.md#locked-mathematical-packages) |
| `python tools/run.py holdfast-parser build-package WORKSPACE LOCK [--output BUNDLE]` | guest | Check the lock and module graph, elaborate in dependency order and optionally publish the bound Gallina bundle |
| `python tools/run.py holdfast-parser diff-contract BASELINE CANDIDATE` | guest | Compare [authored public declarations and effect clauses](../docs/language/first-release.md#public-api-evolution) for one module |
| `python tools/run.py holdfast-parser scip WORKSPACE LOCK --output DIRECTORY` | guest | Export the [offline mathematical package index](../docs/tooling/tooling-protocols.md#locked-mathematical-package-index) and its exact source and generated files |
| `python tools/run.py holdfast-parser scip-check WORKSPACE LOCK DIRECTORY [--require-complete]` | guest | Recheck all SCIP bundle bytes and optionally require full authored-reference coverage |
| `python tools/run.py holdfast-parser qualify-scip-reader READER` | guest | Exercise imported definitions, references, implementations and freshness in the pinned independent SCIP reader |
| `python tools/run.py holdfast-parser qualify-remarks READER` | guest | Read [specialization decisions](../docs/tooling/tooling-protocols.md#compiler-decisions-and-performance-traces) through the pinned LLVM bitstream converter and remark counter |
| `python tools/run.py holdfast-parser bsp WORKSPACE LOCK [LOCK ...]` | guest | Serve the [locked package graph](../docs/tooling/tooling-protocols.md#locked-mathematical-package-builds) over BSP 2.1.1 stdio |
| `python tools/run.py holdfast-parser qualify-bsp-client` | guest | Run the pinned Neovim build client against successful, failed, cancelled and stale builds |
| `python tools/run.py holdfast-parser debug-simulator --qualify` | guest | Check the [packet assembly simulator](../docs/tooling/tooling-protocols.md#packet-assembly-simulator) against expected stops, registers, capability observations and fault paths |
| `python tools/run.py holdfast-parser check-arithmetic SOURCE` | guest | Replay [partial word-operation equations](../docs/tooling/elaboration-prototype.md) and audit their kernel assumptions |
| `python tools/run.py holdfast-parser check-grades SOURCE DEFINITION` | guest | Report [graded computation and type demand](../docs/tooling/elaboration-prototype.md#pure-graded-source-replay) under `NatExact`. Select [bounded allowances](../docs/tooling/elaboration-prototype.md#bounded-natural-grades) with `--domain NatBound` and [graded box replay](../docs/tooling/elaboration-prototype.md#graded-box-source-replay) with `--modal`. Use both flags for [bounded graded box replay](../docs/tooling/elaboration-prototype.md#bounded-graded-box-replay). |
| `python tools/run.py holdfast-parser emit-web SOURCE FUNCTION --output MODULE.mjs` | guest | Export one [Boolean function](../docs/tooling/pure-prototype.md#boolean-web-output) after exhaustive Node execution and kernel replay |
| `python tools/run.py holdfast-parser qualify-web` | guest | Check four independent Boolean web-client tables and two corrupted output modules |
| `python tools/run.py holdfast-parser source-map SOURCE --output NEW_DIRECTORY` | guest | Export mathematical Gallina and its [generated-source map](../docs/tooling/tooling-protocols.md#generated-source-maps) for source and proof lookup |
| `python tools/run.py holdfast-parser packet-example HEX` | guest | Execute the [packet walkthrough](../docs/tooling/packet-walkthrough.md) on up to eight input bytes using the lowered C and a local C11 compiler |

Repeat `--path` to prepare multiple files in one run. Add `--check` to report
formatting findings without writing.

The test runner reports executed and skipped cases separately. It skips slow
cases by default and skips cases whose lane or toolchain is unavailable. Use
`test --slow` to include slow cases in the current lane. On Windows, run the
test command inside WSL to exercise guest and kernel cases.

Run `python tools/run.py holdfast-borrow-compare --measure` to sample the Rust
analysis in fresh compiler processes for each pinned configuration. The report
records the first invocation and five subsequent samples after a discarded
warm-up. Each sample records monotonic elapsed nanoseconds and the compiler's
raw pass times in seconds and resident memory at pass boundaries in bytes. The
processes run sequentially with uncontrolled operating-system caches. Accepted
cases still link and execute their observation tests outside the sampled runs.

## Validation profiles

`validate` combines the usual `gate` and `test` handoff. It runs one command at a
time and defaults to four test workers; `--jobs N` selects another positive
worker count. The gate shares one indexed document corpus between repository
and Markdown checks. Sequential execution keeps proof and editor checks from
competing for the editor workers' time budgets.
Each run writes per-step logs under `out/validation/`. A failed or timed-out step
stops the profile and prints its log path and a bounded tail for diagnosis.

`validate --full` requires the pinned Sail and Rocq switches before qualification.
It includes slow behavioral cases, live editor interoperability, isolated
generated tests, fresh checked-parser support qualification, syntax campaigns
and elaboration/kernel replay. Syntax campaigns already include parser
qualification and the
[pure parser comparison](../docs/tooling/parser.md#pure-parser-comparison). On
Windows, the full profile runs the guest behavioral suite in WSL as a separate
step. On Linux, the local suite supplies guest coverage. The guest test step
requires the native toolchain. The
[first-slice qualification](../docs/language/first-release.md#first-slice-qualification)
defines separate executable and admission evidence.

`validate --static` runs only `typecheck` and `markdown`. The broader `gate` also
checks authored HoldFast examples through the checked parser and therefore needs the
native runtime, including WSL on Windows. The
[static CI workflow](../.github/workflows/static.yml) uses the narrower profile
on Ubuntu and Windows stock runners. It provides automatic Python and Markdown
regression checks. Hosted execution follows the
[shared workflow](../AGENTS.md#git-workflow-and-worktrees).

## Dependency and version policy

- Use the Python minor version specified by `project.requires-python` in [tools/pyproject.toml](pyproject.toml).
- **Exact checker pins**: `dependency-groups.dev` in [tools/pyproject.toml](pyproject.toml) pins exact versions of `ty`, `ruff`, and `rumdl`, resolved with `no-build = true`, `python-downloads = "never"`, and `exclude-newer = "3 days"` in [tools/uv.lock](uv.lock).
- **Reviewed checker schemas**: [tools/ty.toml](ty.toml), [tools/ruff.toml](ruff.toml), and [tools/rumdl.toml](rumdl.toml) are validated against [tools/ty-config.schema.json](ty-config.schema.json), [tools/ruff-config.schema.json](ruff-config.schema.json), and [tools/rumdl-config.schema.json](rumdl-config.schema.json) before any checker runs.

<a id="checked-references-in-source-comments"></a>

## Checked references in source comments

Inline Markdown links in source comments and Python docstrings (`[label](target)` and `[label](target#fragment)`) are checked by `python tools/run.py check` across tracked `.py`, `.hf`, `.ml`, `.mli`, `.mll`, `.mly`, `.v`, `.c`, `.scm`, `.mjs`, `.js`, `.css`, `.yml`, and `.yaml` files. Relative paths resolve from the containing source file's directory against the Git index, and `#fragment` anchors resolve against the target Markdown document's headings and `<a id="...">` bookmarks.
