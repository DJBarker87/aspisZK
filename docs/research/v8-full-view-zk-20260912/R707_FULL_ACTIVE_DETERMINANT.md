# R707: Full active determinant factor

This verified target extends the R705 213-dimensional result to a source-shaped 214-dimensional polynomial matrix with one extra active coordinate. It proves the exact full determinant factor and that the polynomial determinant is nonzero under the stated field hypotheses.

The successful target is `AspisV8R19/R707FullActiveDeterminant.lean`, SHA-256 `3369c8638dda2132231ad174d6bcfa5f0c126c3a3fc2fbbe41c9d8445f891d9a`, compiled at source revision `f5cc2d80b723c5c45252aa9a0b63c4697590c0b3`. Final run `1791128118253816000` exited 0 in 2.01 s, peak Lean-child RSS 3,283,540 KiB, swap 0. It used the pinned Lean 4.32 cache, `-j1 -M4500`, systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The target proves `polyChord_eval` for every field value `c`, the exact source-shaped top-row polynomial pivot, and the full row-update correspondence. Its `full_det_factor` theorem is

```lean
(fullMatrix half).det = (polyMatrix half).det *
  (Polynomial.C (half / 2) * Polynomial.X ^ 2)
```

The resulting determinant polynomial is nonzero assuming `half ≠ 0` and `(2 : F) ≠ 0`. All five complete `#print axioms` outputs contain only `[propext, Classical.choice, Quot.sound]`.

The imported local source pins from the successful receipt are: R705 SHA-256 `40443c2d14853e11351f056cd945069eab1ccd330f5986cb8e4f007ebc71ffbd`; R706 SHA-256 `c1a0dc8612efde831dc15a2f86ef7f167ec543424be511e2d0c38bbad94fa952`; R704 SHA-256 `5719276f9c922fb4d0be4446330e7cffbfb775cc36dd47edd6e0c5da03818ac9`; R699 SHA-256 `f778ddac9dee189eae42b2fc5f29ff69bd97bdb3813dbd1d54dfc62c469263bb`.

All three attempt source snapshots, logs, and receipts are preserved in `evidence/r707-full-active-determinant/attempts/`. The first two attempts failed: the direct application of the earlier generic determinant helper produced elaboration/type errors, and a follow-up proof attempt reached Lean's kernel excessive-memory error while checking the determinant factor. The final source proves the row-operation, full-update, and block determinant steps directly in the target and compiled under the same cap. The failed attempts are retained with their exact full axiom outputs; no larger cap was used.

The result proves a polynomial determinant is nonzero and the evaluated chord-row identity for arbitrary `c`. It does not prove that the determinant is nonzero for every sampled normalized-circle prefix, or establish the actual Rust scatter execution, shared challenge law, H1 residual compatibility, or privacy/security closure.
