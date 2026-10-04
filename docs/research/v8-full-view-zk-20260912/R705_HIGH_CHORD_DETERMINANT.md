# R705: High-channel chord matrix determinant

This verified Lean target proves a determinant fact for the source-shaped 213-dimensional high-active scalar chord matrix and its one-variable polynomial extension. It does not establish the full 214-dimensional determinant or a result at arbitrary sampled `c`.

The successful target is `AspisV8R19/R705HighChordDeterminant.lean`, source SHA-256 `40443c2d14853e11351f056cd945069eab1ccd330f5986cb8e4f007ebc71ffbd`, compiled at source revision `905924ec07abbfc01f1f7f21fb189375ecff57b1`. Final run `1791127720366944000` exited 0 in 1.48 s, peak Lean-child RSS 3,271,120 KiB, swap 0. It used Lean 4.32, `-j1 -M4500`, systemd `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`.

`scalarMatrix_eq` proves the chosen scalar matrix is exactly `2 • blockMatrix`; `scalarMatrix_det_ne_zero` gives its determinant nonzero assuming only `(2 : F) ≠ 0`; `polyMatrix_eval_zero` identifies the polynomial matrix at zero with this scalar matrix. Therefore `polyMatrix_det_eval_zero` proves the determinant polynomial is nonzero at zero, and `polyMatrix_det_ne_zero` proves the polynomial itself is nonzero. All five complete `#print axioms` outputs contain only `[propext, Classical.choice, Quot.sound]`.

The direct local dependencies were pinned as follows: `R702ActiveScalarEmbedding.lean` SHA-256 `8baf43401eb90595ed58c4375e7f95d5b8ef0b24b6daabed142e4a90b08c54f8`; `R703ActiveBlockMatrix.lean` SHA-256 `9861064212747471f6bb0fd3d69440ae2edc7f6693909b55edb1a225de3130ec`. The source-boundary identity used by the subsequent 214-dimensional route is in `R699SourceTopChordBoundary.lean`, SHA-256 `f778ddac9dee189eae42b2fc5f29ff69bd97bdb3813dbd1d54dfc62c469263bb`.

All three attempts, including the two failed proof drafts with their `sorryAx` reports, are preserved under `evidence/r705-high-chord-determinant/attempts/`. The first remaining proposition is to prove how the full 214-dimensional matrix determinant polynomial evaluates at arbitrary `c` after the R699 row operation. The extra-coordinate determinant factor, normalized-circle substitution/domain, actual sampling law, native scatter bridge, and privacy proof are not established here.
