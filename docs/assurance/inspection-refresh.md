# Inspection and editor maintenance rehearsal

## Frozen cycle

The baseline is `14e450e184325c06646a00986bd2554b70dae588`. This cycle
coordinates three adopted tools that consume the same pure compiler identity.

| Consumer | Baseline | Candidate and independently expected behavior |
| --- | --- | --- |
| Offline [inspection reader](../tooling/tooling-protocols.md#pure-development-snapshot-increment) | Inspection schema 6 | Schema 7 binds the Python executable and configured shared interpreter library. Reload the exact source and find `F` and `x` with their original types. |
| [Boolean comparison preview](../tooling/authoring-tools.md#checked-boolean-comparison-previews) | Preview schema 1 | Schema 2 binds the migrated producer. Replace `x == false` with `!(x)` at the same source span. Both programs must return true at false and false at true in Rocq. |
| [Versioned editor action](../tooling/lsp-prototype.md#local-rename-previews) | Compact source-dependency digest | The worker and server compare the complete new producer identity. Pinned Emacs 30.2 and Eglot 1.17.30 apply the expected edit to an unsaved overlay and refuse the stale document version. |

The fixture is a module `M` with `public bool F(bool x) => x == false;`.
Keep the editor's Unicode comment and unsaved text. Retain the baseline
and candidate publications against the same path and source bytes. Refuse
old publications in the new consumers and new publications in the restored
consumers. Change one interpreter input independently and require that the
compact worker digest changes. Roll back the complete checkout in an isolated
worktree, reopen its own original evidence, rerun the consumers and restore the
candidate. Source, parser, prover and editor releases stay fixed for this cycle.

The budget is 90 elapsed minutes of agent work and 30 minutes of timed
qualification commands. Stop to reprice the cycle if either limit is exhausted.
Record human, agent and command time separately. Any later cycle needs a new
inventory and estimate under the [maintenance allocation](../../PLAN.md#q25da).

## Result

The accepted candidate is `c8fbe5b1f0c87772e69b61ac68f8a4e010aaff70`.
On 2026-11-22 one detached checkout ran the four generations in order. The
same fixture path and bytes were used throughout. Each row includes a fresh
compiler export, offline symbol lookup, lint preview, Eglot application and
Rocq replay of the two functions.

| Generation | Inspection / preview | Previously saved publications checked | Command wall time |
| --- | --- | --- | ---: |
| Baseline | 6 / 1 | n/a | 17.564 s |
| Candidate | 7 / 2 | Both baseline publications refused | 16.650 s |
| Rollback to baseline | 6 / 1 | Both baseline publications reopened and both candidate publications refused | 23.927 s |
| Restore candidate | 7 / 2 | Both candidate publications reopened and both baseline publications refused | 21.299 s |

The baseline and rollback produced the same compact producer digest,
`bbc57bcd82be33e42f7433af2235c2fd15bf72c5f599a4644fe2c849a7d83d0c`.
The two candidate runs produced
`73a9fb315ac2a7a27370975d7c0015ae502624300409b3963a4357b23dfd254f`
with CPython 3.14.4 on Linux ARM64. Its interpreter image digest was
`abdc62cb0f94cb09ca34f034e7c48bc757e6a64c0628bb67cf9a0870023e1e34`.
The [interpreter binding regression](../../tools/tests/test_vela_inspection.py)
replaces each image separately at a fixed Python version and compiler source
inventory. Both changes invalidate the compact identity used by the editor.

### Consumer and kernel observations

Save this exact UTF-8 fixture with LF line endings and one terminal newline.

```vela
// 😀 keep == here
module M;
public bool F(bool x) => x == false;
```

`vela inspect check.vela` produced a checked snapshot. A fresh invocation
of `vela inspect check.vela --snapshot saved.json --query query.json` read it
with a `symbols` request carrying the issued schema number and snapshot digest.
The two declarations were function `F` returning `bool` and parameter `x` of
type `bool`. The new reader required `interpreter_sha256` on an old record.
The restored reader rejected that additional field on a new record.

`vela lint-preview check.vela --line 3 --column 28` selected byte span
`[56, 66)`. Revalidating the preview in the corresponding checkout's locked
Python environment returned the exact bytes with `!(x)` at that span.
The source SHA-256 was `80ee0e0116b84021e58ce46f2fd199e8a22ba628cf644e89210a59ffd0eb1b36`
and the edited SHA-256 was `dc7e36ac16d24abdb4f29124725e0853bf9b754d9946f79fa8999701c6919381`.
The new consumer refused the baseline schema before checking an edit.
The baseline validator rejected the changed candidate preview fields.

Emacs appended `// unsaved` on a new line. Eglot requested `refactor.rewrite`
and `quickfix` at zero-based line 2, column 28. The first response contained
one edit spanning columns 25 through 35 at version 1. The second contained
zero actions. Eglot applied the edit, kept the Unicode comment and unsaved
line, then refused the same version-1 action at version 2. The on-disk
bytes still matched the original digest. The wire responses matched the
observed action in each session. The executable and Eglot library matched the
[pinned client hashes](../../tools/toolchain/lsp_rename_clients.py).

For each source, `vela emit` produced a separate Gallina module. The two
following independent observations were appended to each output. Rocq 9.3.0
compiled both files and `rocqchk` recursively checked both compiled libraries.

```coq
Example checked_false : Vela_M.f_F false = true. Proof. reflexivity. Qed.
Example checked_true : Vela_M.f_F true = false. Proof. reflexivity. Qed.
```

### Compatibility, security and cost

Roll out the schema, reader, preview validator and editor worker together.
Retain old publications with the exact checkout and interpreter that produced
them for rollback. The old compact worker digest covered source dependencies.
Two interpreter images with the same displayed version could share that digest.
The new compact digest incorporates the executable and configured runtime
library bytes under stable role names. Hashing uses the existing bounded,
regular-file reader and checks for replacement during reading. The rollout
uses the existing upstream pins and the editor's read-only authority. Standard
library contents, loaded extensions and the operating system are outside this
inspection digest. It supplies freshness for these development tools.

Agent wall time from worktree creation through the final replay was 10 minutes
15 seconds. Observed human intervention took zero minutes. Timed
acceptance subprocesses used 79.440 seconds across the four completed runs.
An initial rollback attempt used another 11.054 seconds before the probe was
corrected to use the locked checkout environment. These are wall times with
no CPU-time or developer-throughput interpretation. General repository
validation is accounted for separately. The budget covered this completed
cycle only.
