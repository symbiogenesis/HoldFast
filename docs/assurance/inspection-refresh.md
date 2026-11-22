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
