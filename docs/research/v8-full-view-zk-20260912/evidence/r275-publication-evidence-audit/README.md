# R271–R275 saved evidence audit

saved evidence only; no Lean, host execution, or proof reruns

Audit result: **PASS**.

Each accepted bundle is checked for inventory and SHA-256 consistency, equality of the saved source copy and promoted target, source hash, saved exit/wall/RSS/swap metrics, full axiom output against both manifest and `axioms.txt`, foundation names, pinned revision, and runner resource/Lean flags.

| Target | Copy and checksums | Metrics | Axiom reports | Runner caps | Result |
|---|---:|---:|---:|---:|---:|
| R271 | pass | pass | 3 / pass | pass | pass |
| R272 | pass | pass | 2 / pass | pass | pass |
| R273 | pass | pass | 2 / pass | pass | pass |
| R275 | pass | pass | 4 / pass | pass | pass |

R271, R272, R273, and R275 use the saved source revision `9dacc9b7a141bdf618136511a4ec783a3983245e`. Their runners record `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and Lean flags `-j1 -M4500`. Full per-target values and axiom declarations are in `audit.json`.

R273 retains three distinct failed proof runs, each with nonzero status and a checksummed log. R275 retains a separate prerequisite failure: its earlier run could not find the compiled R273 object. This is recorded as a dependency/setup failure, not conflated with the three R273 theorem-proof attempts.

This audit reports saved evidence integrity and metadata only. It does not rerun Lean or decide whether any proof closes a semantic or release obligation.
