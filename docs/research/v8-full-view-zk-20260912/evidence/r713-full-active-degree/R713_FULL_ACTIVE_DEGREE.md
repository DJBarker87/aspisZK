# R713: Full active determinant degree

This focused Lean target proves that the full source-shaped active determinant polynomial has natural degree at most 214. It uses Mathlib's matrix-pencil determinant-degree theorem and R710's exact index cardinality.

Canonical target: `AspisV8R19/R713FullActiveDegree.lean`, SHA-256 `0af1423c1e5ebe0e83b127f37ae3fa2c614e8eb6a631f7f0b5fc208b1ed58a51`, compiled at source revision `a5e3046384337bf9a833a613cc72ae440d23741a`. Green run `1791129070858262000`: exit 0, wall time 1.28 s, peak Lean-child RSS 3,273,696 KiB, swap 0. Pinned Lean 4.32 cache, `-j1 -M4500`, systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

`fullMatrix_linear` writes each entry as an affine polynomial in `X`: `X` times the linear-coefficient matrix plus the constant matrix. `full_det_degree` applies `Polynomial.natDegree_det_X_add_C_le` and R710's `index_card : Fintype.card J = 214` to prove `(fullMatrix half).det.natDegree ≤ 214`. Both complete `#print axioms` outputs contain only `[propext, Classical.choice, Quot.sound]`.

The direct local dependency `R710SelectedActivePolynomial.lean` is pinned to SHA-256 `cff02943fe6b61f2ffde5c45425c325ec91d60b5be9ad9c7807bff95fba2a454`. The Mathlib theorem comes from `Mathlib/LinearAlgebra/Matrix/Polynomial.lean`, SHA-256 `c4213a9fc48a9dcb289e1562bbfecd723d4eb208228c0bbdd4da9e37c6f74d68`.

The exact successful source, receipt, log, runner, and complete axiom output are preserved under `evidence/r713-full-active-degree/`. This degree bound does not prove the determinant polynomial is nonzero at an admissible point or yield any probability loss by itself. The next missing steps are an explicit admissible `u` witness for the cleared one-variable polynomial and the nonzero-MvPolynomial/finite-field root-count argument. It does not establish an actual source challenge law or end-to-end privacy/security.
