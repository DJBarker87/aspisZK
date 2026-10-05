# R815 active diagonal determinant units

For every `k : Fin 41` with `k ≠ 0` and `k ≠ 6`, the compiled theorem proves that the determinant of the selected source matrix diagonal block `diagonalSourceBlock k` is a unit. The proof dispatches over the finite block index, rewrites each block using its already compiled source-to-certificate equality, and uses the corresponding pinned certificate inverse theorem. Blocks 0 and 6 are excluded explicitly; no inverse is replayed here.

This is only a statement about these diagonal blocks. It does not establish the determinant or rank of the complete reordered source matrix, because the lower off-diagonal zero structure and exceptional blocks 0 and 6 remain. It does not establish privacy or soundness.

The successful target source checksum, revision, resource caps, time, RSS, zero-swap result, direct import hashes, and full axiom output are in the final run receipt. Every failed attempt is retained. The only axiom dependencies of the successful theorem are `[propext, Classical.choice, Quot.sound]`.

The row/block source bindings it consumes are recorded in `../evidence-complete/`; no selected verifier source or CU result changed for this theorem.
