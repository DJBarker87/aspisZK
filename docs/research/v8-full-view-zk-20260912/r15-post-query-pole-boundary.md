# R15 post-query pole boundary

Source inspection: 2026-09-19. Privacy base `f1e77d14`; selected underlying
revision `9e432896a4e1515efebe940b71fd9b4f9f009189`, recovered performance
SHA `5ded0dbae42449f22e698819d4174f13cf2e9e93f0a195e228011690e008d456`.

The selected performance source constructs `pts` from fibre IDs `0..256`,
four points per fibre. Before q22 it computes the 1,024 quotient evaluations
and unwraps each inverse of

`L(x,y) = abc[0] + abc[1]*x + abc[2]*y`.

Only after interpolation and the first relation fold does it call
`stress_queries`, whose ordinary branch samples 22 distinct IDs from `0..2^18`.
Thus the pre-query inverse checks cover **256**, not **262,144**, fibres.
Reaching that cut certifies nonzero denominators on the interpolation set;
it is not a full-domain pole-freedom certificate.

The actual `opened_values_prepared` path reconstructs points at the selected
IDs and computes their chord denominators. It can return `Error::Domain`;
the host unwraps that result before writing its proof. The optimized norm
inversion path and the reference differential do not erase this obligation.

This does not prove that a pole exists. A separate geometric argument about
the sampled OOD chord might rule out all evaluation-domain poles, or bound
their probability. It must establish that fact for the actual OOD sampler
and its conditioning, not assume it from this 1,024-point interpolation.
Likewise it is premature to charge arbitrary independent pole loss after
conditioning on the entire queried prefix: the chord and its poles are then
fixed, and query selection must be related to that fixed set.

`tools/audit_r15_q22_source_slice.py` now locks the literal 256-fibre setup,
pre-query inverse/interpolation order, and post-query opening call against
the authenticated source image. This is a source-text regression, not a
formal source-semantics proof. No host build or unchanged execution is needed
for this change; no production code, negative regression or assumption changed.

## Compiled algebraic advance

`lean/AspisV8R15/CircleChord.lean` defines precisely the source rational map
`P(t)=((1-t²)/(1+t²),2t/(1+t²))` and determinant chord, and proves:

```
L(P(r)) = 4*(u-t)*(r-t)*(r-u) / ((1+t²)*(1+u²)*(1+r²))
L(-1,0) = 4*(u-t) / ((1+t²)*(1+u²))
```

The two corresponding nonzero theorems require nonzero rational-map
denominators, `4 ≠ 0`, distinct OOD parameters, and (for the finite rational
case) a domain parameter distinct from either OOD parameter. These are
explicit algebraic premises, not hiding assumptions. Both identities and
both nonzero consequences compiled in the existing cached `AspisFormal`
workspace with `lake env lean -j1 -M1800` on the individual file.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Initial two factorization identities | 0 | 14.49 | 1363279872 | 0 |
| Final leaf with both nonzero consequences | 0 | 6.59 | 1364525056 | 0 |

All four `#print axioms` results contain only `propext`, `Classical.choice`,
and `Quot.sound`; no `sorry` or custom axiom. No full manifest replay was
run: this is a new isolated generic leaf, not a release aggregation.
The source-text audit also passed with exit 0.

Source `circle.rs::secure_ood_circle_point_from_parameter` rejects singular
parameters and parameters in CM31; `inactive_row_binding.rs::to_gamma`
requires two distinct returned points. These support the intended route,
but the new Lean leaf does **not** yet instantiate the QM31/CM31 embeddings,
rational parameter recovery for every base-field circle point, or correctness
of the selected optimized norm-inversion code. The generic algebra must not
be reported as complete source pole-freedom.

Next proposition: establish the source OOD chord's pole set on all `2^18`
query fibres (or its event-specific effect on q4/q6), alongside the outstanding
fresh-address query law. Then account for remaining sampler failures,
authentication/terminal correctness, the host's corruption checks and final
publication. Do not substitute the pre-query interpolation checks for these.
