# R377 selector coordinate polynomial lemmas

Status: prepared byte-identity promotion and focused proof evidence; uncommitted. No unchanged recompile was performed during this promotion step.

The promoted module is `lean/AspisV8R19/R377SelectorCoordinateDegree.lean`; its exact copy is in `promoted-source/`. Both files have SHA-256 `86eeaa805425c1c1122b9cbebf171326dc1450bcc11c417b3c91e24f0c4c8c08`. This generic module proves four statements over a field `F`: `selectorPolynomial_degree`, `selectorPolynomial_eval`, `weightedSelectorPolynomial_degree`, and `weightedSelectorPolynomial_eval`. The selector domain is `Fin 10`; the arbitrary weighted row family is `Fin n`, with `bits : Fin n → Fin 10 → Bool` and `coeff : Fin n → F`. The false factor is exactly `1 - line z j k`. The degree results have the stated bound `if j ∈ coords then 1 else 0`; the evaluation results use `Function.update z j x`. No selector-degree premise is assumed.

The direct R374 dependency is promoted `AspisV8R19.R374SingleCoordinateDegree.lean`, SHA-256 `cf9c64577d06c8cb96df204fa34f8832b3b604d3ca6867de2299022eea1fa518`. The source-point dependency is `AspisV8R19.SourceStatementPoints.lean`, SHA-256 `418236a0c336733d73f41d151b5d010a241649eaa4fb9f06d43e842dcf0ca447`. The focused Lean runner itself records direct local import hashes in each receipt.

Lead review accepted the exact four theorem statements, premises, and selector factor construction. The accompanying R374 selector split census is included under `source-route/` only as source provenance: it records the `0..5`/`6..9` split and observed block/local routing, and does not establish that these generic polynomial definitions correspond to source execution or close a terminal-degree obligation. This promotion makes no Rust source correspondence, privacy, or release claim.

## Focused run record

All four saved runs use revision `bb93bebdd1f943b91bd283e85a3ab1a08dc881c7`, runner SHA-256 `d178bfcf47ebe981d552571b5f23f06394193a79f3949e01c758a92877f9d4ea`, `lake env lean -j1 -M4500`, systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`. GNU-time maximum resident set size is the Lean child process measurement; the runner labels systemd wrapper peak separately and does not treat it as aggregate child RSS.

- `1790951344531605000`: exit 1, 1.02 s, 2,285,548 KiB RSS, swap 0. Failed because `unfold weightedSelectorPolynomial` had nothing left to unfold after the finite-sum tactic had reduced the goal. The failed elaboration printed interim `sorryAx` for downstream declarations; this is not part of the successful result.
- `1790951374239780000`: exit 1, 1.09 s, 2,286,932 KiB RSS, swap 0. Failed because `natDegree_mul_le` was incorrectly applied as a function.
- `1790951403732264000`: exit 1, 0.96 s, 2,284,868 KiB RSS, swap 0. Same API-shape issue remained in the revised line.
- `1790951426811815000`: exit 0, 1.03 s, 2,297,784 KiB RSS, swap 0. All four complete `#print axioms` reports are exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

The run inputs, raw logs, receipts, and source snapshots are preserved in `runs/`. `verify_evidence.py` checks copy identity, all saved run receipt/log/input hashes and statuses, the final successful axioms report, direct-import hashes, and the route-only census copy. `SHA256SUMS` covers the complete evidence directory contents except itself.
