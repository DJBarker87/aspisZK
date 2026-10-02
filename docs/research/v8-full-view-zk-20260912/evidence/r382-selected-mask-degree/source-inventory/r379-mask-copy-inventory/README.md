# R379 selected mask and Copy model inventory

This read-only inventory traces the selected R117 state-only mask Horner and Copy terminal from frozen R373/R368 source copies, then compares them to saved R369/R374 model routes. It makes no new source-semantics claim, introduces no premises, and ran no Lean/compiler tools.

The exact mask expression is `H(L0) + (1 + L16^26) * G`, with `L0 = Σ(3+22i)z_i` and `L16 = Σ(275+150i)z_i`. `H` is Horner evaluation of q26…q0. C1 and mask-only claims provide the scheduled tower-rotated coefficients; the schedules cover exponents 0 through 26 except 23. The exact expression source excerpts and line ranges are in `selected-source-excerpts.txt`.

Copy expands the first six challenge coordinates into 64 high selectors and the final four into 16 low selectors. Endpoint row selectors are a high/low product. The selected feature closure routes through the tensor/tag/finish basis gathers. For the two producer and two consumer slots, source forms four chi-minus-value denominators and two weighted numerators, then computes `P*(h1*C+Cn)-C*Pn`; the result is multiplied by `active`. The composition starts from that result, folds 24 semantic and four Poseidon lanes, and applies equality/H1 terms.

Closest existing formal models: R374/R376 model one-coordinate point and table-claim degrees; R378 models absorbed claims plus two fifth-power rounds; R10 CopySlope models the scalar Copy residual and terminal H1 response skeleton. None inspected provides the selected mask source identity or a natDegree model for selector-dependent Copy data. The exact remaining gaps are listed in `inventory.json`. The R374 route’s existing boundary remains: Copy and semantic helper expressions must be represented and bounded from the selected source; this package does not choose those proof statements.

`SHA256SUMS` covers this package except itself.
