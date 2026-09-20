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

## Natural-basis bridge — 2026-09-20

Base privacy revision `3c61406c`. `lean/AspisV8R16/NaturalCoverage.lean`
now compiles `natural_eval_surjective` and `natural_four_slot_coverage`.
The first constructs a right inverse as the retained monomial-to-natural
conversion composed with the inverse Vandermonde matrix. Injective roots
prove the Vandermonde determinant nonzero; surjectivity is a conclusion,
not an added assumption. The second applies this map to the four signed
channel targets and uses the compiled four-slot inverse. It holds for every
n over a field with nonzero 2 and 4, injective roots and nonzero x/y.
Thus n=22 uses four channels of 22 natural coefficients, not just monomials.

The maintained `CircleNaturalBasis` imported all of Mathlib. The first
attempt to import it hit the 2600 MB Lean allocation cap during interpreter
loading (exit 134, wall 41.59 seconds, peak RSS 4241899520 bytes, swaps 0).
It was not retried with a larger cap. `NaturalBasisCore.lean` contains
exactly the retained source declarations and proofs, replacing only that
broad import with Vandermonde, nonsingular inverse and Colex dependencies.
`tools/check_r16_natural_basis.py` checks byte-exact equality against Git
revision `406790e520fa48da4ed7ed0a8e0bb27b9d23625d` and pins the maintained
evaluator source; it passed. No theorem statement or proof was weakened.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Predecessor output attempt without explicit package root | 1 | 4.25 | 667664384 | 0 |
| `FibreInterpolation.lean`, produce missing import artifact | 0 | 9.57 | 2006810624 | 0 |
| Broad-import `NaturalCoverage.lean` | 134 | 41.59 | 4241899520 | 0 |
| Slim `NaturalBasisCore.lean`, before Colex import | 1 | 10.70 | 1958543360 | 0 |
| Slim `NaturalBasisCore.lean`, final | 0 | 5.42 | 1979203584 | 0 |
| `NaturalCoverage.lean`, final | 0 | 12.51 | 1990000640 | 0 |

The missing Colex import provided the existing bit-index sum simplification;
the source-exact proof body stayed unchanged. All Lean jobs used cached
`/Users/dominic/ZK/AspisFormal`, `lake env lean -j1 -M2600`, and explicit
`-R` pointing at this pack's `lean` directory. Local `.olean` outputs are in
`target/r16-lean/AspisV8R16`; prepend `target/r16-lean` to the Lake-provided
`LEAN_PATH` for the dependent leaf. The unchanged interpolation predecessor
was compiled only to produce its missing import artifact. Both new theorem
audits report only `propext`, `Classical.choice`, `Quot.sound`. No Rust or
host replay was repeated for these proof-only changes.

## Remaining boundary

The new Lean endpoint now reaches the four natural-coefficient channels.
The next precise proposition is that the actual source mask lift, followed
by the implemented T and circle encoder, equals that four-channel map with
coefficient positions `4*k`, `4*k+1`, `4*k+2`, `4*k+3`. The transport and
concrete factor correspondence are checked by basis tests and exhaustive
domain enumeration, not yet one composed kernel-checked Rust refinement.

Most importantly, raw surjectivity is not a full-transcript privacy proof.
The staged host now exercises common prover/verifier basis transport and
profile binding (see `R16_SOURCE_INTEGRATION.md`). It still needs universal
soundness preservation and a joint posterior argument
including earlier messages and all remaining disclosures. The source seed,
shared oracle and publication laws remain separate obligations. No full
privacy claim or production integration follows from this milestone.
