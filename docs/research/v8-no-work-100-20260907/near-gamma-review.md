# Near-anchor gamma cover and component-point binding

2026-09-08. Research branch `research/v8-no-work-100-20260907`, starting from
`a33f4f6b2a11b52680597a5f849a63fe221f3fcb`. This continues the
[row repair](row-binding-review.md). The supplied follow-up is preserved in
[evidence/near-gamma-proposal.md](evidence/near-gamma-proposal.md).

## Result and decision

The proposed pre-gamma cover has a rigorous interpolation construction.
The new Lean development constructs one original-code component tuple,
covers every 9,301-close original-code candidate at every allowed gamma,
and gives that same tuple at least **245,609 complete fibres** of component
agreement (982,436 symbols). It never requires agreement on the entire
support of any gamma combination.

The sequential gamma/row game also has a new event-level theorem. It permits
a gamma-dependent corruption support and requires a game only on the
predefined near-candidate event; other gammas contribute zero to this
restricted event. In the ideal model, the resulting component-point-binding
ceiling is

```
max(63/(k-1),
    28/(k-1) + 25/(k-1) + 24/k + choose(9556,22)/choose(262144,22))
 = 53/(k-1) + 24/k + choose(9556,22)/choose(262144,22),
k = (2^31-1)^4.
```

Its display value is **105.1451901644 bits**. The arithmetic is exact in
[near-gamma-results.json](near-gamma-results.json); logarithms are display only.
The new theorem chain supplies the previously missing *mathematical*
construction and gamma cancellation argument in this near-anchor regime.
It does not supply an actual Rust-to-game constructor or payment extractor.

QM31 q22 remains the primary research direction under **40,282 bytes**.
There is now a smaller substantive recovery obligation: accepted executions
without a sufficiently close image-valid anchor, plus conversion of a
correctly bound recovered tuple into a resource-bounded valid payment witness.
A global 100-bit result is still absent.

## Construction and hypotheses

Fix all 29 received component words, the original linear code C, and the
nonzero parameter set G. At each fibre/slot let v be the scalar-power
polynomial in gamma, with degree at most 28. Define Good from these fixed
objects alone: g is good iff v(g) is within 9,301 complete fibres of some
word in C. No actual sampled gamma, decoder output, candidate membership
certificate or later final polynomial enters this definition.

If Good has fewer than 64 elements, the probability of entering it under
fresh uniform nonzero gamma is at most 63/(k-1). This is charged before
conditioning. If it has at least 64, choose 64 distinct good parameters and
one close codeword for each. The Lean proof uses a simpler sufficient
incidence certificate than the supplied convexity argument:

* Total missing incidences are at most 64*9301 = 595,264.
* A fibre lying in fewer than 61 supports misses at least four supports.
  Consequently at least 113,328 fibres lie in 61 or more supports.
* Double counting 29-subsets proves some 29 selected supports share more
  than 9,557 fibres, because
  `9557*choose(64,29) < 113328*choose(61,29)`.

Interpolate the codewords at these 29 distinct nodes. Linearity puts every
coefficient in C. On their common support the received and interpolated
curves coincide identically. Any later 9,301-close codeword shares more than
256 fibres with this interpolant evaluated at its gamma, forcing equality
under the code overlap hypothesis. This quantifies over *every* qualifying
candidate, including one selected after gamma.

For a fibre where at least one component differs from the interpolated
tuple, a nonzero degree-at-most-28 difference can vanish at no more than
28 of the 64 chosen nodes. Thus it contributes at least 36 missing
incidences. At most floor(595264/36) = 16,535 fibres differ componentwise.
The construction is noncomputable; enumerating all good gammas is not a
promised efficient witness extractor.

The concrete fibre bridge uses the source's map
`(fibre,slot) ↦ 4*fibre+slot`, proves its agreement with
`fibreSlotEquiv`, and derives a 256-complete-fibre overlap cap from the
existing 1,024-symbol initial-code overlap theorem. It does not reinterpret
the V8 quotient matching set as the V7 raw-word matching set.

## Gamma, row and relation timing

C1 precedes its early challenges. C2 can depend on lambda/chi but is fixed
before the component batch gamma. All three rows of 29 point claims, the
first OOD vector, the second OOD point, and the second OOD vector follow the
existing sequential order before gamma. The tuple just constructed depends
only on the fixed received words/code, so it is fixed at this boundary even
if the 87 claims are false.

Choose a row with a false component evaluation before gamma. Its error
polynomial has degree at most 28 and is nonzero. The new game charges its
at most 28 roots. At other gammas, any close image-valid quotient anchor
reconstructs U=LQ+I equal to the constructed component batch, provided the
chord/image/original-code bridge holds. Its gamma-batched point row is wrong.

The inactive scalar may depend on gamma but must precede kappa. The repaired
ordinary discrepancy is
`i+kappa*e0+kappa^2*e1+kappa^3*e2`.
Ordinary weights/scalar and the quotient prefix precede tau. Response0
precedes alpha0; final256 can depend on alpha0; the schedule precedes rho;
every later response precedes its own alpha. The reused noisy game includes
these later adaptations and the shifted degree-q query polynomial.

`gamma_then_row_near_event_bound` specifically allows the support
`corrupt gamma` to vary and restricts probability to Good. It does not
demand a fictitious anchor for every gamma. Its point-row identity and
NoisyGame input remain algebraic interfaces to instantiate from the
constructed tuple and the real verifier. The file does not claim these
interfaces are translated Rust facts.

## Theorem and interface status

| Item | Result and exact scope |
|---|---|
| NearGammaSupport | Symbolic support incidence and common-subset construction |
| NearGammaCover | Interpolation in a linear code; all close candidates covered |
| NearGammaOwnSupport | At least 245,609 fibres of component equality for the interpolated tuple |
| NearGammaDichotomy | Constructs the tuple internally; combined code membership, own support, and universal near-candidate coverage |
| NearGammaArithmetic | Small exact integer certificate inputs, no added axioms |
| NearGammaFibreBridge | Source fibre indexing and complete-fibre overlap from existing initial-code overlap |
| RowSeparatedImageGame | Fixed error-polynomial root charge followed by the causal row/relation/query game; supported-event and variable-corruption variant |
| Actual scalar-power word assembly, point evaluation and chord reconstruction | Mathematical specialization explained above; no completed translated-source constructor |
| Compact response/terminal identities | Reused JointImage/Robust interface lemmas and differential evidence in robust-recovery-review.md; no new source translation |
| C1 descent, semantic/copy/ownership recovery | Earlier own-support descent result reusable, but complete tuple-to-payment proof and extraction resource bound remain open |

Lean replay details, source hashes and axiom audits are in
[near-gamma-evidence.json](near-gamma-evidence.json). A modular generic
theorem is not a theorem that actual verifier acceptance constructs its
hypotheses. In particular, the full code-range/quotient/point-functional
instantiation and actual event partition are still source obligations.

## Total accepted mass and the remaining budget

Retain the source/provider partition rather than equating every `none`
with one prequery event:

| Actual/replay outcome | Treatment |
|---|---|
| Actual parse failure, abort or sampler exhaustion | Not acceptance when the actual callback fails closed |
| Accepted actual run, replay failure, abort/fuel exhaustion | Retain replay/extractor-failure mass; generally not prequery measurable |
| Restored challenge zero/mismatch | Keep its coupling obligation at the restoration boundary |
| K13 rejection/query/fold/list cases | Keep the actual later observation; shifted batching can accept a nonzero query residual on exceptional rho |
| K14 width29 failure | Neither equivalent to no near anchor nor removed by this theorem |
| Provider certificate returned | Still require component-point binding, semantics, ownership and checked witness extraction |
| Valid witness returned | Extraction success |

Within a correctly coupled ideal execution, classify by the anchor set
determined by received quotient and chord before kappa:

1. No B-close image-valid anchor: retain U_no_anchor. The existing invalid-image
   game handles the exact-polynomial invalid-image subclass (and the earlier
   noisy game supplies its stated nearby-anchor extension); their charges
   must be composed jointly, not applied after conditioning on tau success.
2. Such an anchor exists: apply the new pre-gamma cover dichotomy.
   Small Good is charged by 63/(k-1). In the dense case one fixed tuple
   covers every such anchor, with own-support recovery.
3. Some component point claim is false for that tuple: new gamma-then-row
   bound, including subsequent relation/query collisions.
4. Component points correct but inactive false, or actual final differs:
   retain the previously proved row/off-final bounds at their proper
   prefixes. These local relation charges overlap the four repairs already
   counted here; no mechanical second 24/k charge is justified.
5. Correct bound tuple but no checked valid payment witness: retain
   U_tuple_to_witness. Codeword existence does not establish this event's
   probability or an efficient extractor.

The near-anchor charge consumes about **2.826%** of a 2^-100 budget.
The exact difference 2^-100 minus this local charge is recorded only as
local headroom. No numeric global allowance is claimed: authentication,
actual source/replay coupling and other semantic/extraction terms have not
been justified in a composed V8 theorem. The historical 396430 numerator
is not imported as a single semantic term. Source correspondence and
toolchain trust are theorem/assurance obligations, not fabricated small
failure probabilities.

The ideal law uses fresh conditionally uniform challenges. Fiat–Shamir
prequeries, restorations, forks, retries and running time require a separate
resource-bounded lift. No positive work/grinding term is used. There is no
claim for unlimited offline search or quantum security.

## Permanent regression classification

* A: the original 9,557-common-fibre construction remains a same-support
  counterexample. Its small-support zero anchor is outside this B=9301
  regime; the relaxed family result remains relevant.
* B: paired 9,556-common-fibre construction, including full-degree roots,
  remains outside the new near-anchor coverage claim. OOD-compatible
  family membership is not assumed.
* C: high-J (252,843 common, 9,301 other fibres) is covered by the
  pre-gamma tuple construction on its own support. Extra exceptional
  combined-zero fibres still need not recover componentwise. Its earlier
  pointwise subevent remains a lower bound, never an upper bound.
* D: pre-OOD T512 has invalid image; reuse the joint image gate result.
* E: zero-fold/nonzero-image kernel still excludes a final256-only image test.
* F: shifted-batch and later-repair collisions remain charged. The supplied
  late-inactive countermodel still cancels universally if timing is violated.

Existing production-field regression suites were not repeated because their
source did not change. The supplied finite cover/row tests were reproduced
and their limited scope is preserved in evidence/near-gamma-supplied.log.

## Engineering, privacy and next experiment

The body census is unchanged:
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282`.
The 64 parameters are analysis objects; no protocol queries, nonces,
certificates, padding or extra rounds were added in this continuation.
The inherited research callback still hashes 16,384 public weight bytes
before tau and still has the previously recorded query/authentication cost.
No Rust change, full-transaction CU, SBF result, full prover timing or prover
peak-RAM measurement is produced by these Lean edits.

Full-view privacy remains an adaptive simulation problem for OOD answers,
tau-dependent relation responses, final256 and authenticated openings.
These proof changes do not modify that view and do not complete its
simulation proof. The existing image/row changes still need that proof.

The next decisive experiment is a bounded small-code search for accepted
**no-near-anchor** executions with the repaired row and carried image
relations enforced, then a proposed universal tail bound for exactly that
event. A counterexample must retain its ordinary/image discrepancy and
actual final/query matching count, not just its intermediate decoder
failure. If this event cannot be bounded within the remaining justified
budget, q22 needs a concrete design change. q23/41,527 bytes and quintic
q22/42,984 bytes remain unapproved controls.

## Bounded V7 inactiveExact audit

At the research base revision, v6_transcript.rs reads/absorbs inactive_claim,
then obtains kappa, uses scales [1,kappa,kappa^2], and combines the scalar.
The selected v7_verifier.rs callbacks invoke that relation preparation;
no independent equality of inactive_claim to the committed inactive
functional was found in this path.

The formal dependency is explicit:
V7Tag73ExactOperationalK15Stage has an inactiveExact structure field;
V7Tag73OperationalRelationSourceFacts takes inactiveExact as an argument;
V7Tag73ExactCausalK15Reduction passes material.source.inactiveExact.
Thus the inspected source bridge assumes the premise rather than deriving
it from acceptance. The existing conditional theorem remains intact.
This is a missing acceptance-to-premise bridge, not a demonstrated complete
payment forgery. The repository's V7 Tag73 feature is opt-in; the documented
deployed V5 path is distinct. This continuation changes neither path.
