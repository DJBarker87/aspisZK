# R709: Chosen-column channel basis

This Lean target proves the exact selected-channel basis representation of each high-active source column at the scalar `alpha = 1` layer. It is an algebraic model identity over all row indices, not a native execution or privacy theorem.

The canonical target is `AspisV8R19/R709ChosenColumnBasis.lean`, SHA-256 `3cb21ea43a79427e13068c3e46a2de197623c2c4b3eb80c49d922d9ba88e7422`, compiled at source revision `a9e6939ffd3544fbb8423914a5d0ba873bda715c`. Green run `1791128736041580000` exited 0 in 3.50 s, peak Lean-child RSS 3,360,844 KiB, swap 0. The pinned Lean 4.32 run used `-j1 -M4500`, systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

For every `j : High` and `r : Nat`, `chosenQ_single_basis` identifies `chosenQ (Pi.single j 1) r` with the difference of the two unit vectors at channel coordinates `base + slot` and `base`, where `base = 4 * (22 + selectedColumn(j).val / 3)` and `slot = 1 + selectedColumn(j).val % 3`. `extraQ_basis` proves the extra column is `unitVector 1018 - unitVector 1016`. The supporting `coeff_single` computes the coefficient response to one basis column.

All complete `#print axioms` outputs are preserved. `coeff_single` and `chosenQ_single_basis` depend only on `[propext, Classical.choice, Quot.sound]`; `extraQ_basis` reports `[propext]`. Imported local source pins: `R702ActiveScalarEmbedding.lean` SHA-256 `8baf43401eb90595ed58c4375e7f95d5b8ef0b24b6daabed142e4a90b08c54f8`; `R706ExtraActiveColumn.lean` SHA-256 `c1a0dc8612efde831dc15a2f86ef7f167ec543424be511e2d0c38bbad94fa952`; `AspisV8R17/WeightedScatter.lean` SHA-256 `5a33cf1c7f5fa122bf3f2bc94ac6c2d4f51a25446f565faf8e3d6e20da413e0c`.

All seven focused attempts are preserved under `evidence/r709-chosen-column-basis/attempts/`, with exact source snapshots, logs, and receipts for six failed drafts and the final green source. No target was rerun during packaging.

The boundary is the exact source-shaped channel basis at `alpha = 1` for all rows. It does not establish native execution, masking behavior, the full H1 relation, privacy, or security. Those source and cryptographic arguments remain open.
