# R574 sparse-G core polynomial

This milestone proves that the free-parameter algebraic `coreMap` has a nonzero determinant polynomial of total degree at most 1084. It is a model result over `[Field F]` and `[NeZero (2 : F)]`, for arbitrary `half`; it does not establish that a challenge prefix is admissible or sampled with any particular law.

The polynomial entry uses three distinct sourceChord coefficient families, for `(1,0,0)`, `(0,1,0)`, and `(0,0,1)`. Each family has four constant sourceChord evaluations, giving the specified twelve constants per entry. The proof establishes linearity of `coreMap`, its matrix representation, equality of polynomial evaluation with `coreMatrix`, nonvanishing by evaluation at `(alpha,a,b,c)=(1,2,0,0)`, and the 1084 total-degree bound from the generic determinant-degree lemma. The excluded witness is only an algebraic witness; it is not asserted to be an admissible sampled prefix.

The exact source is [R574SparseGCorePolynomial.lean](lean/AspisV8R19/R574SparseGCorePolynomial.lean), SHA256 `ccd4bab7796221eada233ba04de5c83a09e8565f69009d24115d7a822abc4b16`. It is byte-identical to the source that passed the scratch proof.

The canonical module-path check compiled `AspisV8R19/R574SparseGCorePolynomial.lean` on the pinned host in the cached Lean 4.32 workspace. Run ID `1791085246392110000`; source revision `8ca13fb20dcb9bb026681f93ac16c18d486397e5`; exit status 0; wall time 2.99 seconds; peak Lean-child RSS 2,289,676 KiB; swap 0. Limits were `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean flags were `-j1 -M4500`. The full log and receipt are in `evidence/r574-sparse-g-core-polynomial/attempts/`.

The report retains all 28 focused attempts (23 failed, 5 successful), including every attempted source snapshot, log, and receipt. The original green scratch check and canonical path check are separate artifacts. The final printed theorem axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; none contain `sorryAx`. The pinned direct-import hashes and exact full axiom output are recorded in the receipts.

The next missing obligations are normalized-circle polynomial nonvanishing, the selected high-section/low-query repair and its actual-source correspondence, followed by the full G-image, privacy simulator, and probability-loss arguments. This milestone proves no actual normalized-circle nonvanishing, full G-image compatibility, end-to-end privacy, or security claim.
