# R16 universal raw-coverage argument and exact checked boundary

Date: 2026-09-20. Base privacy revision `0d5aba9d`.

## Algebraic argument

Write each source fibre as `(x,y),(x,-y),(-x,-y),(-x,y)` and its
line root as `t=2*x²-1`. The low coefficient block splits into four channels

`A(t) + y*B(t) + x*C(t) + x*y*D(t)`.

For arbitrary four target values on a fibre, their signed sum/difference
combinations divided by 4, 4y, 4x, and 4xy recover the four channel targets.
For n distinct roots, Lagrange interpolation realizes each channel with a
polynomial of degree less than n. Thus 4n coefficients suffice to realize
every four-slot observation on n distinct fibres, provided x,y,4 are nonzero.
This is deterministic, for every schedule meeting those conditions; no
random-query probability or rejection filter is used.

`lean/AspisV8R16/FibreInterpolation.lean` proves the four-slot inverse and
the quantified interpolation theorem for arbitrary n and any field. It
constructs four degree-bounded polynomials; it does not assume surjectivity.
At n=22, each channel uses 22 coefficients: 88 total.

The source uses the natural line basis rather than monomials. Retained
`AspisFormal/CircleNaturalBasis.lean` proves degree triangularity and an
invertible natural/monomial conversion for every width. Applying that
conversion to each channel is the mathematical bridge to coefficients
0..87. R16 currently relocates 89 independent existing balanced mask
directions there; the extra direction is not needed by this interpolation
argument. Do not silently count it again after conditioning on other views.

## Complete finite source-factor check

The new unit test
`r16_source_low_factors_match_four_slot_polynomial_channels` enumerates every
one of the 262,144 fibre IDs and all four slots. For each it checks actual
`CircleEncoder::encode_c1_basis_value` at coefficient indices
1,2,4,8,16,32,64 against y, x, and successive doubling factors beginning at t.
It also checks that the complete set of line roots has 262,144 distinct
values. The source evaluator defines a general row as the product selected
by that row's bits. Therefore these factors cover every row below 128,
including the proposed first 88 coefficients.

The earlier exhaustive domain test established canonical nonzero x/y for
every fibre. That unchanged test was not repeated. The new factor test
passed. This is exhaustive executable evidence about the fixed source
domain, not a kernel extraction of Rust semantics or all field operations.

## Exact execution evidence

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Lean four-slot inverse alone, cap 1800 MB | 0 | 8.64 | 1361592320 | 0 |
| Lean final interpolation leaf, cap 2600 MB | 0 | 12.09 | 1972633600 | 0 |
| New release source-factor test | 0 | 17.02 | 510017536 | 0 |

Lean: cached `/Users/dominic/ZK/AspisFormal`, `lake env lean -j1` on the
individual changed file. Both audited final theorems depend only on
`propext`, `Classical.choice`, `Quot.sound`.
Rust: `cargo test --offline --locked --release --jobs 1 -p aspis-prover
--lib r16_source_low_factors -- --nocapture`; one passed, zero failed;
test time 0.10 seconds, compilation 16.50 seconds. No full manifest or
unchanged full regression ran. Existing negative regressions are unchanged.

## Remaining boundary

The new Lean theorem stops at the four monomial-channel representation.
The natural-basis theorem is retained and inspected, but a single composed
Lean endpoint joining it to this theorem and the R16 transport is not yet
compiled. The concrete factor correspondence is checked by executable
enumeration, not a formal Rust extraction.

Most importantly, raw surjectivity is not a full-transcript privacy proof.
The candidate still needs complete prover/verifier basis transport, correct
profile binding, soundness preservation, and a joint posterior argument
including earlier messages and all remaining disclosures. The source seed,
shared oracle and publication laws remain separate obligations. No full
privacy claim or production integration follows from this milestone.
