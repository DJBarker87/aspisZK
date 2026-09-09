# Causal fork collector: agreement counts do not supply coherence

Research base: `532ade2064e533602902fc9ae5b4dd90f9207131`.
The new bounded optimized diagnostic is green. The frozen full search is
unchanged and was not rerun; no NUC, Lean, SBF, production, or deployment job
was used.

The decisive result is a counterexample to an **unqualified** reduced-game
inference from at least seven qualifying alphas to a common two-fibre,
coherent quotient. The eight predeclared prefixes have 10–13 qualifying
alphas, yet their selected maximizing policies have no quotient coherent on
more than five alphas. Even allowing every tied optimal response and final
choice, their largest common-two-fibre groups have only four or five alphas.

This does not contradict a theorem that *assumes* shared support, nor the
already proved high-agreement geometry. It is not a payment forgery, a failure
of every witness extractor, or a QM31 probability bound.

## Frozen model and predeclared scope

[`fork_collector_control.rs`](experiments/fork_collector_control.rs) includes
the unchanged [`helper_far_moment.rs`](experiments/helper_far_moment.rs) in a
module. Its full-search main is never called. The field, circle fibres,
eight-coefficient natural basis, 8-to-2 fold, shifted kappa rows, carried image
weights, fixed early C1, degree-two helper curve, and both fixed component OOD
vectors are exactly those of the [completed search](helper-far-moment-review.md).

The new test predeclares both helper profiles, both OOD modes, and gamma 1 and
2, with kappa=tau=1 throughout. Each inactive scalar is the already recorded
compatible-moment policy from the earlier complete causal search:

| Profile | OOD mode / chord | Gamma | Inactive |
| --- | --- | ---: | ---: |
| 0 | 0 / 2x | 1, 2 | 2, 18 |
| 0 | 1 / 2y | 1, 2 | 3, 8 |
| 1 | 0 / 2x | 1, 2 | 13, 1 |
| 1 | 1 / 2y | 1, 2 | 9, 11 |

There is no new seed, helper, gamma, kappa, tau, or inactive search. In
profile 0, gamma 1 and 2 happen to give the same normalized received word
and incoming claim for each OOD mode. Their identical results are therefore
not presented as independent evidence.

For each fixed prefix, the diagnostic exhausts all 361 permitted response0
choices and all 361 final coefficient pairs at every alpha in F19. Response0
has free c0,c1 and reconstructed c4=`claim/4-c0`; c2,c3,c5,c6 remain zero. The
maximum response score is taken after summing the nineteen fresh alpha
outcomes. Final choices are allowed to depend on alpha, not on future queries.

A qualifying alpha has an actual final with **zero carried prior** and exactly
two matching fibres. It is the zero-prior far pointwise-query event of the
earlier model: q=2, four fibres, and far means more than one mismatching fibre.
For such a final, exactly two of the twelve ordered distinct query pairs pass.
The fixed-prefix moment is therefore `qualifying_alpha_count / 114`. This
diagnostic does not re-average the earlier challenges or rerun rho/tail
optimization. Their causal laws and costs are not replaced by these fixed
prefix values.

## What the collector receives and checks

The producer puts its actual sixteen received values behind `ReceivedOracle`.
The collector sees an explicit oracle identity and canonical indexed reads,
not an expected quotient, a pointer to an honest anchor, hidden randomness,
or a witness. These are **full-oracle ideal reads**, not Merkle openings or a
construction of a real replay adversary. The numerical identity fields are
namespaced fixture identifiers; they are not cryptographic commitments.

Each disclosure has the fixed prefix ID, fixed oracle ID, alpha, and the two
actual final coefficients. The harness holds the same first response across
the alpha forks. It does not assert that a real Fiat–Shamir prover supplies
these records. In particular, the test enumerates alpha values; it is not a
fresh-challenge replay distribution.

`collect` takes four distinct disclosures and performs Lagrange interpolation
separately on the two final coordinates. Nonzero denominator products check
the four-node Vandermonde rank. The result is interleaved using the actual
low-two-bit order

```
q[4*lane + alpha_power],  lane in {0,1}, alpha_power in {0,1,2,3}.
```

The source verifies the resulting fold against all four supplied finals.
`collect(…) = Ok(candidate)` is **not a recovery certificate**: it only
certifies this interpolation/input-boundary step. The separate `audit` reads
the actual received oracle and computes:

- Every slot of the quotient's complete-fibre support, without assuming the
  received word is polynomial.
- Which disclosed finals equal the quotient's fold, and their common actual
  matching-fibre intersection.
- The literal image residual `[q7,2*q6]` or `[q7,-2*q5]`.
- The ordinary scalar discrepancy, image-mixed discrepancy, and every
  coefficient of the carried prior polynomial.
- The cross-product chord transpose against the independent multiply/project
  reference, including the equivalence of zero image residual and zero
  omitted coefficients in this reduced basis.

For every candidate with four or more coherent disclosed alphas, the measured
common matching support equals its actual all-four-slot oracle support. This
is checked from the values, not assumed as a provider membership condition.
Every purported coherent branch is checked; candidates with zero or one
common fibre remain in the output rather than being silently discarded.

The ordinary/image algebra retains the discrepancy

```
ordinary_error - tau*E1(q) - tau^2*E2(q).
```

Its value equals `4*(prior_polynomial[0]+prior_polynomial[4])`. An image-invalid
candidate can have a zero combined boundary at a particular tau because the
ordinary error cancels the image term. Zero combined boundary also does not
make every other coefficient of the prior polynomial zero. The diagnostic
keeps all these quantities separately.

## Exact policy and tie classification

For each prefix the first maximizing response in source enumeration is used,
then the first eligible final in the source's `fi=c0+19*c1` order at each
qualifying alpha. These are deterministic choices, not favorable tie searches.
The selected response, final records, fibre masks and actual zero priors are
all retained in the [green log](experiments/fork-collector-control-v1.log).

All four-disclosure subsets of this selected policy are interpolated and
deduplicated. This exhausts every quotient coherent with at least four of
that policy's disclosures: any such quotient is determined by four of them.
It does not exhaust arbitrary-support coherence for every possible final
tie policy.

A second, exact tie-aware check handles **common support of at least two
fibres** across all optimal response and final ties. There are six fibre pairs.
For each optimal response and pair, two distinct final-domain positions
uniquely determine the final at each alpha. Thus the test can enumerate all
eligible alphas for that pair without enumerating an exponential number of
final policies. Four such disclosures construct its coherent quotient;
all remaining group members and raw oracle slots are checked.

| Profile / mode / gamma | Qualifying alphas | Optimal response ties | Largest coherence, selected policy | Largest common-two group, all optimal ties |
| --- | ---: | ---: | ---: | ---: |
| 0 / 0 / 1 | 10 | 5 | 5 | 5 |
| 0 / 0 / 2 | 10 | 5 | 5 | 5 |
| 0 / 1 / 1 | 11 | 1 | 5 | 4 |
| 0 / 1 / 2 | 11 | 1 | 5 | 4 |
| 1 / 0 / 1 | 11 | 1 | 5 | 4 |
| 1 / 0 / 2 | 11 | 1 | 5 | 4 |
| 1 / 1 / 1 | 13 | 1 | 5 | 4 |
| 1 / 1 / 2 | 10 | 1 | 5 | 4 |

There are **zero** seven-alpha common-two-fibre groups across every tested
optimal response/final tie choice. All reconstructed common-two groups are
image-invalid. The independent image-distance routine again finds distance
three for every received word, consistent with the absence of an image-valid
quotient matching two whole fibres.

The log field `chosen_policy_best_common_two` only counts reconstructed groups
with at least four disclosures: zero there means no such four-node group,
not that no pair occurs once, twice, or three times. This does not affect
the all-optimal-ties maximum in the table, which counts pair occurrences
even below four.

One especially direct regression is profile 0, mode 1, gamma 1. Its unique
maximizing response is `[6,5,0,0,4,0,0]`; all eleven qualifying alphas have a
unique eligible final. Their fibre masks are

```
alpha: 2  3  5  6  7 11 14 15 16 17 18
mask:  9 10 10  9  3  6 10 12  6  3 10
```

No alternative optimal response or final tie can repair that policy's lack
of a seven-alpha shared-support/coherent group. Its largest two-fibre group has
four alphas, yielding quotient `[0,7,0,0,0,7,0,0]` with image residual `[0,5]`.
Its ordinary error is 5, so tau=1 gives combined boundary zero; nevertheless
its prior polynomial `[6,4,16,12,13,0,0]` is nonzero and has only the observed
four coherent zero-prior nodes. This is legitimate challenge cancellation,
not an omitted image check or a contradiction of a polynomial root bound.

## Degree-six criterion and the established high region

For one fixed quotient q, both final coordinates and carried dual weights
are cubic in alpha. Their scalar product has degree at most six. Subtracting
the first compact response therefore gives a degree-at-most-six polynomial.
Seven distinct zero-prior alphas **for that same q** force the entire polynomial
to vanish. The diagnostic implements the coefficient convolution and checks
this implication whenever applicable. The honest controls meet it; the far
policies do not supply its common-q premise.

The [existing pre-image anchor theorem](pre-image-anchor-review.md) already
constructs a common anchor in the high-agreement region under
`5*B + cap < T`, and the
[joint theorem](pre-anchor-joint-continuation.md) connects that geometric
classification to the carried image/row game. Those results are consumed,
not reproved or rejected. Here the linear final code has cap=1, T=4, and the
qualifying far finals have B=2; `5*2+1<4` is false. The new diagnostic concerns
the untreated far geometry, not that established high region.

The earlier 129,942/128,190 qualifying incidences and lower bounds on prefixes
with seven qualifying alphas therefore do not imply the required collector
coverage. A collector needing seven coherent, common-support branches must
account for the branches where this condition is absent. That mass cannot
be called knowledge failure merely from the far label: another recovery
method may work, and these zero-C1 toy fixtures do not implement payment
semantics at all. The numerical QM31 contribution remains unbounded here.

## Positive controls, failures and resources

Two separately predeclared honest image-valid quotient controls use the same
oracle and collector interfaces. Their producer computes genuine full compact
responses by convolving primal and dual coefficients; it is not restricted to
the adversarial two-free-coefficient response subfamily. The expected quotient
is withheld from `collect` and used only for a post-extraction fixture
assertion. Both reconstruct from four disclosures, are coherent at all
nineteen alphas, match all four received fibres, and have zero image, ordinary,
combined and coefficientwise prior discrepancies. They are polynomial-relation
controls, not valid-payment executions.

The bounded collector explicitly tests an aborted attempt followed by four
valid responses, insufficient responses, fuel/cap exhaustion, duplicate alpha,
prefix-ID mismatch, oracle-ID mismatch, and noncanonical alpha/final values.
There are fourteen negative checks plus two successful abort/resume controls.
The positive run uses four attempts and sixteen oracle reads to construct the
candidate, another sixteen reads for its full audit, and five attempts with
one abort in the resume test. It claims no bounded success rate for a real
prover supplying or withholding those attempts.

Reproduction from the research worktree:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_fork_collector_control.sh \
  /absolute/path/to/a-new-fork-collector-log.log
```

The runner uses `rustc --edition=2021 -O -C overflow-checks=yes`, an independent
1 GiB aggregate RSS guard, and a 90 CPU-second cap. It performs no dependency
build and verifies the frozen included source hash. Rust was
`1.93.0 (254b59607 2026-01-19)`.

| Stage | Exit | Wall time | Peak RSS (bytes) | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Optimized standalone compile | 0 | 1.38 s | 168,886,272 | 0 |
| Eight-prefix diagnostic | 0 | 0.51 s | 2,277,376 | 0 |

The arithmetic itself took 0.0738 s. The run checked 54,872 final candidates,
2,665 four-disclosure subsets, 2,553 distinct selected-policy quotient
reconstructions, and 96 tied-response/pair combinations. Total explicit oracle
reads across the diagnostic and controls were 84,256. These are extractor
model reads, not proof bytes, verifier operations or CU.

SHA256 evidence pins:

- New source: `15ce5a0f4618326d06fbd03b4a1c9237a57d28a8b692c0434550d7e5e28ed06c`.
- Runner: `2e34922f150d6fde0207ea5d13d1f76d0a98563d644d03654dbc8d8ffa3e0c03`.
- Green log: `c27b8b773976576c1b054accb437758152f2fde83d357f68e0b888004526d167`.
- Included frozen search: `2e4f615b11754126bd62c5f97cf92a9802d6de03f375ab762d49dee15d081588`.

No Lean proof or axiom audit is claimed for this exact Rust diagnostic. The
40,282-byte body, field/domain/query profile, production defaults and verifier
checks are unchanged. Authentication/replay coupling, full-view privacy,
Fiat–Shamir resource accounting and full-transaction CU remain separate gates.

The next mathematical step must either establish a quantitatively charged
coherence/common-support event in the residual regime or use a different
collector that can recover despite rotating supports. Counting qualifying
alphas alone is no longer a plausible substitute for that step.
