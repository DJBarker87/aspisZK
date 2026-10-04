# R620 actual selected matrix multiplication law

Verified boundary: for every eight exact base-field coordinates `a,b,c,d,e,f,g,h`, the actual captured `r83_matrix` executes and returns a matrix whose decoded column action on `(e,f,g,h)` equals multiplication by `(a+bi)+(c+di)u` in the selected QM31 field, with `i²=-1` and `u²=2+i`.

The source call is present in `actual_matrix_action`, which has no execution, canonicality, coefficient-value, or field-law premise. Its matrix is obtained from R619's actual execution theorem; the four matrix columns are read at bounded Fin indices, decoded from their returned words, and combined in the mathematical field. The proof covers zero and degenerate input coordinates as well as ordinary ones.

This is a coefficient-matrix execution and multiplication theorem. `matrixAction` is an explicitly defined mathematical decoded action, not the actual 38-term integer dot-product implementation. That implementation's no-wrap arithmetic, decoder, constructor, and caller connection remain required. No full quotient extraction, privacy, or soundness claim follows yet.

## Exact focused result

- Target: `AspisV8R19/R620MatrixAction.lean`.
- Final source SHA256: `136002d73ff7d1ff257c937966677280f66f2de49b65fd1b706058a0897c8f59`.
- Run: `1791103336716089000`; exit 0; wall 2.37 s; peak RSS 3,760,872 KiB; swap 0.
- Proof worktree revision: `54ffbc2643511f05b1d1445ef4fa73f6986cbee2`.
- Frozen Rust source revision and extraction provenance are retained by R618/R619 in that commit: `6677d5f1310ff7373301fbd79f186278f772e68a`; actual matrix target `query_arithmetic.rs:422–427`.
- Direct source dependency R619 SHA256: `4f0257cca34db1285c42d4a2e2f00951baadaa9b7d308093a997c7ec2eaf1eac`.
- Direct `ProductCorrectness.lean` SHA256: `4fcf2a646c8c849838aa6925c082af20a681579f4a4e929e9ddda0e24019a37d`.
- Pinned Lean 4.32 cached workspace, `lake env lean -j1 -M4500`, individual systemd caps 5G high / 7G max / 0 swap / 128 tasks.

Both complete `#print axioms` reports (`qm31_product_coordinates`, `actual_matrix_action`) contain only `[propext, Classical.choice, Quot.sound]`. The saved log includes one unused-simp-argument warning; the verified source is promoted unchanged. Earlier coordinate-only and changed action attempts are retained. No unchanged check was repeated for promotion.

## First remaining proposition

Prove that the actual `BetaCoefficients::new` constructor assembles these matrices from the gamma powers and beta weights, and that the actual 38-term `r83_mixed_limb` calculation realizes their field action without overflow and with complete canonical decoding. Source array construction/map/try helpers still need faithful execution binding; they are not admitted as assumptions.

Coherent extraction of the original quotient pair before beta, connection to the quadratic fold, optimized-verifier acceptance implying source-verifier acceptance, whole callback chronology, universal joint C1/H1/G privacy including p0/p2 and adaptive/degenerate prefixes, and the entire published-view simulator and actual shared-oracle probability losses remain unproved.

Verifier source, all security parameters, and the 999,790 / 999,532 CU results are preserved. No CU benchmark, unchanged regression, deployment, transaction, or wallet operation was performed.
