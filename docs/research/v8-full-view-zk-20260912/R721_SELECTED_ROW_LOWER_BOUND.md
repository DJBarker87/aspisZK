# R721: Selected row lower bound

Canonical Lean target: `AspisV8R19/R721SelectedRowLowerBound.lean`, SHA-256 `95c53fe7e0f55c10526530d6dc93efb66a3a16ccf054e14237172150b71c788b`. Final focused run `1791131178610262000` used source revision `dc4a83812c9b0c252412e5ba190cb4b6cb152a82`, Lean 4.32, `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The final run exited 0 in 3.56 s, with peak Lean-child RSS 3,556,628 KiB and swap 0. Both complete axiom reports contain only `[propext, Classical.choice, Quot.sound]`.

R721 proves by one bounded finite-layout decision that high-active source rows 88 through 113 are absent. Combining that with the existing high-active bounds and the explicit `Unit` row 1022 proves `114 ≤ rowCode i` for every selected row.

The evidence retains the initial proof-plumbing failure `1791131159709309000`, final green `1791131178610262000`, the exact R720 source dependency, and the focused runner. This is an integer layout fact only; it does not add field arithmetic, determinant, native, challenge, privacy, or security claims.
