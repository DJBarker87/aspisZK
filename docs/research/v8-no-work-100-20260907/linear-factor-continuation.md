# Retained factors to component curves

Research continuation of `6f1ebbe55fcc6fd008071329d5270aae0521cf9a`,
on `research/v8-no-work-100-20260907`. All new Lean checks run on the NUC,
serially in capped scopes. Existing main work is untouched. No production,
Rust verifier, protocol message, proof-body or deployment change.

## What this continuation changes

The previous endpoint retained an actual polynomial candidate rooted in a
fixed factor family. It did not make those factors component tuples. This
continuation develops a concrete recovery path for **linear-Y factors whose
rational root is polynomial in gamma of degree at most 28**. The statement
constructs its component curve from the equation, rather than receiving a
candidate tuple or provider-success premise.

The complementary non-polynomial-in-gamma and higher-Y cases remain visible.
No estimate of all accepted retained-factor mass is presented as extraction
failure: it includes ordinary honest proofs. Component recovery is also not
yet checked-payment extraction.

## Three different fixing boundaries

1. C1 is fixed before lambda/chi. C2 can depend on those challenges. The
   interpolation parent and its prime factors depend on C1/C2 and are fixed
   before both OOD points.
2. The sequential OOD points/answer vectors select the retained factor
   family before gamma. Each answer still has all 29 scalar-power terms;
   the separate helper curve still has degree at most two.
3. Gamma and later alpha may affect the actual reconstructed candidate and
   final256. The new root-recovery result quantifies over every such later
   candidate. It does not move its selection before those challenges.

The resulting tuple can be fixed before gamma, but not thereby before
lambda/chi. The early-C1 projection, own-support and semantic/copy arguments
must still establish their earlier causality separately.

## Linear-factor recovery

Write a fixed factor as `F = A(X,Z) Y + B(X,Z)`, with Z the gamma variable.
Suppose its root in `K(X)` is a polynomial `R(Z)` of degree at most 28 and
the polynomial equation `A*R+B=0` holds after the actual field embedding.
This is an explicit class premise, not a consequence asserted for all
retained factors.

Define good gammas from that fixed equation: a code polynomial of the
specified code submodule, with X degree at most 1024, is a root at gamma.
If there are at most 28 good gammas, keep this branch and count executions
whose actual fresh gamma belongs to that set. The sparse-branch property
itself need not be rare. Otherwise choose 29
distinct good gammas and their code polynomials. Lagrange interpolation
constructs each component as an explicit K-linear combination of those
polynomials. Hence every component remains in the same code submodule.
Interpolation over the extension field identifies every coefficient of R;
injectivity of `K[X] -> K(X)` then identifies every later polynomial root,
not merely the 29 chosen nodes.

The source endpoint uses the **range of the actual selected circle-to-GRS
map**, not the whole space of degree-at-most-1024 polynomials. Symbolic
encoder linearity and the existing V7 degree/injectivity results supply
this submodule. Its lifted components are natural-coordinate QM31 message
vectors. This does not yet establish base-field descent of the first 26 C1
components, agreement with the received components on their own support,
or an executable recovery algorithm. Those remain explicit prerequisites
for the later C1/payment chain.

`PolynomialValueInterpolation` and `LinearFactorInterpolation` check these
statements symbolically. This uses the interpolation pattern already used
by V7; it does not import V7's much larger Hensel denominator loss.

The completed selected endpoint is
`SelectedLinearFactorRecovery.actual_message_dichotomy`. Its sparse set is
defined by actual original-code message roots of the fixed factor. In the
dense branch it returns `Fin 29 -> (Fin 1024 -> QM31)` and identifies **every**
later polynomial root with the actual encoder applied to the corresponding
scalar-power message combination. That later root need not arrive with a
separate code-membership, degree or nonzero-denominator premise. For the
`28/(k-1)` ideal interpretation, the input Gamma universe must be all nonzero
field challenges, fixed before sampling—not an adaptively filtered set.

### No uncharged zero-denominator branch for a prime linear factor

`PrimeFactorRegularity` proves a stronger deterministic prerequisite.
A primitive positive-Y factor cannot specialize to the zero polynomial at
any gamma: otherwise `Z-gamma` divides all Y coefficients, so its constant
lift divides F, contradicting primitivity. For a linear factor and an actual
polynomial root, `A_gamma=0` would also force `B_gamma=0`. Thus every such
root has `A_gamma != 0`, derived from the actual prime-factor membership.
This means nonzero **as a polynomial in X**, not nonzero at every evaluation
point; it does not replace the source's chord-denominator checks. No new
exceptional probability is required for this case.

### What two OOD identities establish for monic linear factors

For a monic linear factor the unique curve is literally `-F.coeff 0`, a
polynomial in X and Z. If its Z degree exceeds 28, one nonzero high-Z
coefficient H(X), chosen from F **before OOD**, must vanish at every point
where an answer of degree at most 28 gives a polynomial identity.

`MonicFactorOOD` constructs a single nonzero obstruction E(X) by multiplying
these chosen coefficients across the fixed parent factors. The sum of the
factors' X degrees is at most the parent's X degree. Therefore E has degree
at most **114687** for the selected interpolation parent, with no additional
factor-count multiplier. An excessive-degree retained monic factor forces
both actual OOD points to be roots of this same E. Answer adaptivity does
not change this implication.

The generic pair-root cardinality bound is `deg(E)^2`. Assigning a
probability still needs the appropriate OOD sampler law. The source samples
a QM31 parameter outside CM31 through a bounded rational-circle sampler,
and the second point is required to differ from the first. Uniform sampling
from all of QM31 is not its literal law. Neither the finite count nor the
source inspection is an actual Fiat-Shamir theorem.

The companion helper regression is now classified completely at the
polynomial-root level: for nonzero gamma,
`(X-a)*U = N(gamma)` holds exactly when `gamma=b` and `U=0`.
Thus it lies in the small-good branch (at most one nonzero gamma), rather
than contradicting the dichotomy or being excluded through an assumed
polynomial curve. This is not a classification of all proof acceptance.

## Selected copy constraints to amount aliases

The parallel bridge reuses the generic V7 LogUp characteristic-polynomial
and Wronskian proofs without importing the obsolete 183-link registry or
historical numerical error inventory. It uses the actual active subset of
the selected 136 links.

Given the source local copy residuals, total and inactive helper identities,
and every applicable slot-pole exclusion, it derives an explicit partition:

- all active weighted tuple aliases hold; or
- one nonzero lambda polynomial, fixed from the table before lambda, vanishes
  at lambda, with degree at most `16*n`; or
- one nonzero chi Wronskian, fixed after lambda but before chi, vanishes at
  chi, with degree strictly below `2*n`.

Here n is the actual active-link count, not 183. The lambda witness is a
coefficient of the difference of two characteristic polynomials; there is
no factorial matching union. Source tag injectivity and characteristic
guards are discharged separately over actual QM31. These are conditional
deterministic implications: proof acceptance enforcing their premises and
the table's early-C1 fixing time are still required before charging root
probabilities.

## Remaining accepted-extraction accounting

| Class | New treatment | Still required |
|---|---|---|
| Accepted suffix without a good covered quotient | Existing bound reused unchanged | Actual source/authentication/replay lift |
| Good quotient outside the retained identity-factor family | Existing `117077/(k-1)` bound reused once | Same source/FS lift |
| Retained monic linear factor with excessive Z degree | Constructed pre-OOD double-root obstruction | Actual finite-sampler probability bridge |
| Linear prime factor with polynomial-in-Z root degree <=28 | Sparse-good or constructed actual-code component curve | Own-support, C1 subfield/early-prefix descent and payment extraction connections |
| Other non-monic rational-in-Z or higher-Y factors | Retained explicitly | New classification/recovery bound |
| Recovered tuple without a checked payment witness | Not removed | Early-C1 semantic constraints, decoder/context/settlement endpoint and resources |
| Authentication/source mismatch; replay abort, fuel, missing response or cached/advance mismatch | Not encoded as one convenient prefix event | Total actual extractor accounting |

The original/paired root-product cases, high-J own-support case, T512 image
obstruction, zero-fold image kernel, shifted row/rho and later-repair cases,
radius-boundary recovery and mixed-C1 minority-target regression remain.
The new helper specialization control classifies polynomial roots, not a
full payment acceptance event. No unchanged regression suite was replayed.

## Ledger and costs

[linear-factor-ledger.json](linear-factor-ledger.json) records exact rationals
and null global charges. Its independent class screens are approximately
214.385315 bits for the stated uniform-distinct OOD-parameter model and
119.192645 bits for hitting one fixed factor's sparse good-gamma set.
Neither number is a new composed V8 security level. The first still needs
the actual bounded-sampler law, and the second still needs the selected
family/event and extractor composition.

The previous local reduction ceiling remains approximately **104.366053
bits**, with retained accepted/extraction mass unbounded. New conditional
class counts must not be mechanically added to it as a global certificate.
The historical 396430 inventory, duplicate relation repairs, content and
derivative charges are not added. Full-view privacy and resource-bounded
Fiat-Shamir remain separate. Grinding credit is zero; no quantum claim.

Body: `697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes.
New verifier operations/messages/bytes: none. New CU, full prover time and
SBF measurements: none. NUC proof-check timings are not prover benchmarks.

## Checked endpoints and reproduction

| Endpoint | What is checked | Remaining boundary |
|---|---|---|
| `SelectedMonicCover.exists_selected_classification` | Same reconstructed Q, fixed pre-OOD parent, degree-114687 double-root obstruction | Non-monic/higher-Y classification and OOD sampling law |
| `PrimeFactorRegularity.prime_linear_root_regular` | Root-bearing prime linear factor has nonzero polynomial A_gamma | Pointwise chord denominators are different checks |
| `SelectedLinearFactorRecovery.actual_message_dichotomy` | Sparse good challenges or actual natural-coordinate component messages; arbitrary later U | Stated polynomial-in-gamma root class, own support, early C1 and executable extraction |
| `RationalHelperSpecialization.polynomial_root_iff` | All nonzero-gamma polynomial roots of the helper pole control | Not a full semantic/payment execution |
| `SelectedCopyAliasQM31.qm31_source_roots_or_aliases` and `transfer_amount_aliases` | Exact selected collision/alias partition and seven source amount edges | Acceptance enforcing local premises, canonical amount constraints and checked witness |

Twelve new focused leaves passed, with 72 named standard-only axiom audits.
These are kernel-checked algebraic/source-shaped interfaces and literal
selected-encoder/layout connections, **not a Rust-to-Lean translation of the
complete verifier**. No dependency/package replay was needed. Failed
attempts and exact source snapshots are retained; local errors were fixed
symbolically, without increasing memory/recursion limits. The concrete
QM31 constructor failures were repaired using generic wrappers and named
encoder equalities. The seven-cell lookup uses a small field-free layout
certificate instead of broad simplification of the whole source table.

```
python3 docs/research/v8-no-work-100-20260907/experiments/linear_factor_ledger.py --check-recorded
python3 docs/research/v8-no-work-100-20260907/experiments/audit_linear_factor_evidence.py --check-recorded
```

For an intentionally changed leaf, the recorded runner invokes cached
`lake env` Lean on the NUC with `-j1 -M9500`, MemoryHigh=8GiB,
MemoryMax=10GiB, MemorySwapMax=0 and CPUQuota=200%. Do not rerun unchanged
leaves to reproduce metadata. See [the full execution record](linear-factor-build-evidence.md)
for commands, pins, exits, timings, RSS, swaps and source/olean hashes.
No Lean or substantive arithmetic build ran on the laptop.
The staged whitespace check reports one extra blank line at EOF in the
preserved failed `selected-copy-alias-core-nuc-v1-source.txt` snapshot.
Its exact attempted bytes are intentionally retained for the provenance
audit. The staged check excluding that one historical snapshot passes.

## Decision

This is a genuine component-recovery advance within a precisely defined
factor class, plus a source-shaped step toward payment amount aliases.
It does not establish global 100-bit extraction or production readiness.
The present q22 grammar remains the research target; no size relaxation or
protocol change is introduced.

The next decisive mathematical experiment is to classify the remaining
**linear factors with a gamma denominator** using the two OOD identities:
derive a nonzero resultant/leading-coefficient obstruction before OOD,
including degree drops, or exhibit a causal counterexample. This would
extend the proved recovery class; it must not presume the rational root is
already a degree-28 polynomial. Higher-Y factors and component own-support
remain separate even if that experiment succeeds.

The mathematical cross-review found no algebraic flaw in the stated scope.
It corrected the sparse-event ledger wording: the set's smallness is a
prefix property; only the actual challenge hitting that set is rare.
The milestone notification was sent through the authorized Pushover helper.
