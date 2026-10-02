# R366 universal semantic compatibility route — unverified draft

Campaign HEAD at preparation: 7c588ebcd62955448a0298b3d480aa7e23c408bb.
Target: AspisV8R19/R366SemanticNormalization.lean.
The first attempted compile stopped at missing StructuredCube.olean, before checking any theorem. Eleven missing cached dependency objects are being produced; twelve existing objects are reused. No security gate is closed by this draft.

## The algebra to prove

For every degree-at-most-27 polynomial p with p(0)+p(1)=carry, take the exact stored normalized coordinates

    a = coeff(p,0) - carry/2
    b[i] = coeff(p,i+2), i=0..25.

Then for every field challenge x (including 0 or 1),

    p(x) = carry/2 + a*(1-2*x) + sum_i b[i]*(x^(i+2)-x).

Iterating this identity through all ten original carries gives the exact structured-mask evaluator of the 271-coordinate record. The initial coordinate remains present and may change; it is not assumed zero. Taking two complete records and subtracting gives the difference of the two final carries. Thus equal final carries imply the complete semantic target lies in the kernel of the actual 271-coordinate covector, once the existing source mask-weight bridge and the new normalization bridge are instantiated faithfully.

This is an inverse-normalization argument for arbitrary records. It does not choose a witness-difference basis, infer compatibility from measured ranks, impose a Boolean challenge, divide by a challenge, or exclude a degenerate semantic point.

## Actual-source obligations still required

The retained diagnostic r17_witness_semantic_delta enumerates the literal old/new terminal difference at each of 28 interpolation nodes and every remaining Boolean suffix, records the initial boundary sum, stores c0-carry/2 and c2..c27, and advances carry by Horner evaluation. Its assertions at the two tested prefixes are evidence only. They do not discharge the universal degree, boundary, or final-terminal propositions.

For a universal source instantiation, prove the actual selected terminal's degree at most 27 in each currently varied coordinate, exact interpolation and suffix-sum laws, and every original carry/boundary equality. A degree-27 interpolation routine by itself establishes only the output polynomial's degree, not equality to the terminal away from its sample nodes. Preserve any actual errors/panics rather than assuming these impossible.

At the endpoint, the actual terminal must receive equal public parameters, semantic challenges, and all retained selected point claims. Its nonlinear C1/H1 context dependence must be preserved. Determinism then gives equality of its result, including errors. This needs the exact selected profile's claim routing and complete source binding, not the inverse-only opaque R230 callback.

Successor point coordinates are individually affine in a varied original coordinate, but composition with an arbitrary ten-bit multilinear table can have degree ten. Do not assume successor-point claims are affine. Range-bit squaring, all selectors, public lanes, copy residuals, helper inactive terms, the explicit-linear mask power, structured-G replacement, and the positive-transfer correction must appear in the degree accounting. The explicit-linear^26 times ordinary G term is a candidate degree-27 extremum; this has not yet been proved for the complete source.

The result addresses only the semantic terminal compatibility equation. Universal C1 and H1 retained-view coverage, complete G compatible-image coverage, all pre-beta p0/p2/channel coefficients, legal mask restrictions, posterior bijections, adaptive/shared-oracle and seed laws, commitments, retries/failures/publication, a complete simulator with explicit losses, and soundness remain open.

## Source/version cautions

The tracked R17 diagnostic, the saved R27/R28 stage, and the selected R117 two-swap native profile are distinct pinned artifacts. Do not substitute one for another merely because function names agree. The historical q4/q6 same-public separator and the row-1014 inverse-product/384-row diagnostic stay intact; neither is silently promoted into an attack on the selected two-swap profile.
