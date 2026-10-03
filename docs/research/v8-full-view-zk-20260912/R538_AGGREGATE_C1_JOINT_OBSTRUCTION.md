# R538: aggregate C1 repair and remaining joint G condition

The changed diagnostic compiles. On the one synthetic `zero-low22` case, choosing the 16 C1 corrections jointly repairs the earlier initial-claim obstruction. The source initial claim and all original C1 observation checks pass. Extended H1 also passes. G still has one incompatible target, identified by a complete finite-matrix certificate.

This is a diagnostic result, not a Lean theorem or a proof of privacy/security. The challenge history is deliberately inconsistent: z=0, alpha=0, gamma=kappa=tau=1, OOD parameters j and 2j, queries 0..21, and beta retained from an unrelated honest history. The H1 helper retains the stronger R28 ordinary-polynomial constraints.

## What passed

Each original C1 system has 108 observation rows. The construction retains their full free-variable kernels, then solves four M31 equations for the total source initial claim. That system has rank 4 and 2,250 variables. All 16 C1 systems, 1,408 raw values, 48 point claims and 32 OOD claims pass. Both the source `state_only_initial_mask_claim` and its `r17_relation::initial` adjustment are independently equal before and after correction. The ten mask-only columns and G remain fixed during this step.

The 568-row H1 system passes at rank 544, retaining its legal padding, raw/point/OOD/final and all-seven ordinary polynomial checks. The G system has 626 rows, 1,022 columns, rank 600, and one incompatible reduced row.

## Exact remaining equation

The saved left-kernel certificate is +1 at original semantic row 256, -1 at original point row 359, and +1 at original p2 row 625. Its combination vanishes on every one of the 1,022 original matrix columns. Its RHS is `(2009279124, 375448309, 1725948707, 1391775322)`, which is nonzero in QM31. The lead independently checked canonical limbs, every original column, and the RHS using separate modular field arithmetic.

With `d` the recomputed semantic offset, `rq` the ordinary quotient correction, and `dw = wg - wr`, the remaining compatibility equation is

```
dot(dw, rq) = gamma^27 * d[256].
```

The prior initial-claim obstruction is repaired; the current sequential choice does not satisfy this additional coupling. This does not rule out another joint H1/G correction or a full published-view simulator.

## Source and execution receipts

Frozen R117 revision: `6677d5f1310ff7373301fbd79f186278f772e68a`.

- Diagnostic caller SHA: `85a2e77c4b13a41d406e4f068f7a5e7d8db5c9ae3622954e3bbb31cc3735d9e3`.
- Helper SHA: `7fe7d8b0a21f5a568815749ac4d7516472e369e257767526eb23e05dcf301945`.
- Binary SHA: `846a3c15f25cfc579e8db8d976bda7df6a8a74fc4a51bfa597136908ea56c789`.
- Uncompressed G certificate SHA: `cf20fae1ca4c1eaa581ffe11020ba241a9ab800142c8b2c7de73dfab01f42403`.

| Target | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| Changed optimized focused build | 0 | 11.22 | 550648 | 0 |
| First single-case run | 101 | 25.37 | 250704 | 0 |
| Same binary, missing-certificate recovery only | 101 | 25.59 | 250896 | 0 |

The first build had a diagnostic M31/QM31 dot-product type error; its journal is retained. The certificate-only rerun was necessary because the first run omitted the output-path variable; it changed neither source nor binary. Every NUC job used 5 GiB high / 7 GiB max / zero swap / 128 tasks. Cargo fingerprint evidence records the selected flags. Preserved evidence does not attest the overflow-check environment setting; this limit is explicit. `#print axioms` is not applicable to this Rust diagnostic.

Evidence: `evidence/r538-aggregate-c1-joint-obstruction/`. Historical notes and provenance limitations are retained in `ARCHIVE_NOTES.md`.

## Next proposition

Choose H1 and G jointly so the displayed equation holds, including the actual H1 contribution to semantic coordinate 256, while retaining every earlier constraint. Recompute the complete source semantic difference and all existing G checks. A successful case would remain short of universal joint compatibility, the whole published-view simulator, and the adaptive source soundness bound.

The selected verifier and its 999,790 / 999,532 CU results are unchanged. No CU benchmark or unchanged regression suite was run.
