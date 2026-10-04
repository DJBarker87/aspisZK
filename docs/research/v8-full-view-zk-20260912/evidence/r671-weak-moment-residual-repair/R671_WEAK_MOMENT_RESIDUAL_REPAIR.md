# R671 weak-moment residual repair

Status: focused Lean target is green and reviewed by the lead. This is an unpromoted evidence candidate; no unchanged check was replayed.

R671 weakens the prior conditional structured-G hypothesis. Instead of requiring all seven structured coefficients of the incoming full-index G polynomial to vanish, it requires one structured full source moment and one cross moment. Together with zero first folds for R and G, zero ordinary R coefficients, nonzero scale, quarter, and kappa, and the explicit residual matrix determinant, it constructs a 13-coordinate residual correction. The corrected full-index G has all seven structured and cross coefficients zero for every beta. The correction preserves all modeled 271 sparse coordinates, all three source point functionals, inactive balance, 22-by-4 query roots, and 32 first folds. It also proves the retained full-source p2 boundary.

This is a conditional field-model theorem. It does not show that a legal same-public witness difference supplies the ordinary-R, structured-G, or cross-moment premises. It does not bind the construction to native Rust, the actual callback, the root or determinant law, the shared oracle, a published view simulator, privacy, soundness, or end-to-end security.

Final focused run `1791116143833993000` compiled `AspisV8R19/R671WeakMomentResidualRepair.lean` at source revision `6c7a03a127e8af66babdf1ea3f03c828d6b78769`, SHA-256 `5e88d717087dcc476c6f92d185cc847ca231ad66ac5f576447e64adbccb389b4`. It exited 0 in 1.63 seconds, with 3,319,544 KiB peak Lean-child RSS and zero swap. Its complete `#print axioms` result contains only `propext`, `Classical.choice`, and `Quot.sound`.

The evidence retains four changed failed focused attempts and the final receipt, log, exact snapshots, runner, and direct dependency copies.
