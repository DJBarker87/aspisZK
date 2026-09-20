# R16 compatible G posterior including Final256

Date: 2026-09-20. Base privacy revision `77f73387`.

The new focused test is
`circle_candidate::r16_basis_repair::final_posterior::r16_g_posterior_including_final256_compatible_image`.
It measures a fixed-challenge joint map; it is not an adaptive source
transcript or a full privacy theorem.

## Quotient parametrization

Keep the two component OOD values unchanged. Let the OOD chord be
`L=a+bx+cy`. Parametrize changes to the encoded G polynomial by `c=L*q`,
where q satisfies the source image constraints

`q[1023]=0`, `b*q[1022]-c*q[1021]=0`.

The diagnostic uses 1022 basis vectors for this space: coordinates 0..1020
and the final direction `(q[1021],q[1022])=(b,c)`, with checked b nonzero.
Here the chord coefficient c and the encoded vector c use the conventional
same letter; the implementation stores them separately as `abc[2]` and a
coefficient vector.

Natural-line multiplication by x is the primal of the retained source's
`inactive_row_binding::edges/xt` map. Writing q as E(x)+y O(x), multiplication
by L gives even part `(a+bx)E+c(1-x²)O` and odd part `cE+(a+bx)O`.
The test checks that all coefficients beyond 1023 vanish, both source OOD
evaluations vanish, and every sampled raw value equals L times the raw q
value. It maps the encoded result back through the implemented inverse T
and checks its forward round trip. No mask is resampled.

This is a source-shaped primal implementation with cross-checks, not a
formal extraction of the host's decoder or its complete dependency closure.

## Joint map and result

The 430 QM31 observation coordinates are:

- 82 first-three-cut G semantic coordinates, as in the earlier diagnostic;
- 88 raw G values at the retained q22 schedule;
- 3 original-row multilinear G point claims;
- 256 folded quotient coefficients (Final256);
- 1 original inactive-sum claim, explicitly serialized by the source.

The OOD values are fixed by the parametrization rather than omitted as
unconstrained disclosures. Non-G columns and challenges are fixed. The
single G contribution's batch scalar is normalized to one; a fixed
nonzero gamma power merely rescales its linear contribution. Actual
Fiat–Shamir challenge coupling is not inferred from this normalization.

The test verifies all 22 fold-consistency equations on every one of the
1022 input basis directions. These equations are independent: each has a
nonzero coefficient in its own disjoint four-raw-value block. This gives
the upper bound 430-22=408 for the image dimension.

Elimination returns rank 408. An independent multiplication verifies a
408-row left inverse on the selected original matrix columns, establishing
the matching lower bound. Thus, for this fixed diagnostic, the image is
exactly the subspace satisfying the 22 fold relations: no additional
linear obstruction occurs in this selected view.

In particular, corrections may keep the first 82 coordinates zero and
target any later vector satisfying those relations. This retains the
earlier affine kernel. It does not replace the actual target by 430
arbitrary independent coordinates or ignore the inactive-sum disclosure.

## Execution evidence

Both runs used `/usr/bin/time -l cargo test --offline --locked --release
--jobs 1 -p aspis-prover --lib
r16_g_posterior_including_final256_compatible_image -- --nocapture`.
The expected expensive steps were compilation, then the named small
QM31 elimination and independent certificate multiplication, all optimized.

| Changed scope | Exit | Wall seconds | Peak RSS bytes | Swaps | Test seconds |
| --- | ---: | ---: | ---: | ---: | ---: |
| Initial 429 rows, before inactive claim added; rank 407 | 0 | 21.80 | 523485184 | 0 | 2.39 |
| Final 430 rows plus independence check; rank 408 | 0 | 21.91 | 524730368 | 0 | 2.30 |

Both ran one test with zero failures. Final compilation took 19.19 seconds.
No Lean theorem changed, so an axioms audit is not applicable. No unchanged
host replay or full regression was repeated. Original negative regressions
and production paths are untouched.

## Exact remaining boundary

This closes only a fixed-prefix compatible-image diagnostic through the
first three semantic cuts and the listed linear disclosures. It does not
cover semantic rounds 3..9 or their nonlinear C1/H1 coupling, the relation
polynomials, actual entropy-backed seed expansion, shared oracle, adaptive
query schedule, visible failures, retries or publication. The R14 G-only
final-round obstruction is still valid.

The next essential algebraic step is a joint C1/H1/G correction for actual
witness offsets through the later semantic rounds, retaining this compatible
PCS posterior. A universal theorem must then justify it for the source
challenge law and quantify exceptional mass. These checks do not establish
full privacy or soundness preservation.
