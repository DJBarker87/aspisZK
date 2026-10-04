# R726: Point-factor identity

Canonical Lean target: `AspisV8R19/R726PointFactorIdentity.lean`, SHA-256 `5fe2f7666008dac624a4e0cf3035e561ffd53a51f4efc48ac68ef99ef377f4a5`. Final focused run `1791132160216451000` used source revision `d6a4f48bd785b03ba542c98e7b59fca469ff92ca`, Lean 4.32, `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The final target exited 0 in 0:01.65 with peak Lean-child RSS 3,285,248 KiB and swap 0. Its complete `#print axioms` result is `[propext, Classical.choice, Quot.sound]`.

For every commutative ring, ten-coordinate input `z`, and row `r` whose bits 3 and 2 are both one, R726 proves

`z 6 * z 7 * sourcePointBasis (points z 2) r = (1-z 6) * (1-z 7) * sourcePointBasis (points z 0) r`.

The proof separates the two changing coordinate factors from the common product over the other eight coordinates. It has no division or nonzero premise, so it also covers degenerate `z`.

This records a limitation of the low-only mask-repair construction. It does not establish a privacy leak, a global point dependency, a native-source execution correspondence, or any privacy or security conclusion.

The evidence retains thirteen focused records: unsuccessful direct expansions and finite-product plumbing/probe runs, two explicitly rejected provisional successes, subsequent type/rewrite failures, and final green `1791132160216451000`. The direct source imports and exact focused runner are copied with their hashes in `manifest.json` and `SHA256SUMS.txt`.

The first remaining proposition is the full H1 residual image retaining all three point observations, using directions beyond this low-only support and justified query normalization.
