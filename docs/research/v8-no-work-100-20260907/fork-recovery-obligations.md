# Fork-recovery certificate: obligations and resource contract

Continuation at parent `532ade20`: [fork collector and four-kappa
recovery](fork-collector-continuation.md) completes the four-row deterministic
composition and executes the first bounded collector controls. The historical
status below describes the seven-alpha/three-tau checkpoint; its open
four-kappa item is superseded by that continuation. Access/coherence and
global extraction obligations are not superseded.

Research base: `edb199c12fcc41f00330298b95b4736f60ac6f3a`. This is a
source/theorem map and a proposed bounded-extractor contract, not an implemented
replay extractor, payment-witness theorem, or new numerical security bound.
Both deterministic certificates are now kernel-checked:
[`SevenAlphaRecovery.lean`](experiments/SevenAlphaRecovery.lean) constructs Q,
derives all seven final identities and concludes one mixed equation;
[`ThreeTauRecovery.lean`](experiments/ThreeTauRecovery.lean) retains that same Q
across three tau branches and separates image and ordinary constraints. Their
statements and source were inspected read-only for this report. The four-kappa
composition and the collector remain unproved/unimplemented obligations.
No build was run for this document.

## What the certificate can establish

At one fixed gamma/kappa/tau prefix, retain the same first compact response
and collect seven distinct alpha0 forks. Suppose their finals are each checked
against the same received four-slot oracle on a **common** set S of more than
255 complete fibres, and each has zero actual carried prior. Four forks
recover a quotient vector Q by code-valued interpolation. Agreement on S and
the final-code overlap cap force every collected final to be its actual fold.
The first compact response discrepancy against this one Q has degree at most
six and seven roots, so its polynomial is zero. Its boundary yields

```
ordinaryPrior(Q) - tau*E1(Q) - tau^2*E2(Q) = 0.
```

This is **one mixed equation**. It is not separate image validity, ordinary
row correctness, original component membership, or payment knowledge. The
common-support condition is a sufficient deterministic certificate, not a
claim that every useful extractor must collect that exact support.

The final-polynomial identification needs more than 255 common final-domain
positions. The same threshold also suffices across later tau/kappa forks:
keep Q recovered from the first four branches, and identify every later final
directly by comparing its evaluation with the fold of this Q on the same S.
There is no need to recover a different Q per tau and then use the coarser
full-code overlap cap. A 257-fibre collector remains a conservative sufficient
control, not a necessary threshold. The source uses actual stored indices,
canonical x/y twiddles and four-slot order, not arbitrary points with the same
cardinality.

Q may be constructed **after** collecting these forks. This is legitimate
for a deterministic interpolation-and-seven-roots certificate. It does not
permit a 6/k probability estimate against a target retrospectively selected
after alpha. Such a probabilistic estimate needs its own causal fixing or
covering argument.

## Separating the carried constraints

| Collection | What must remain the same | Deterministic consequence |
| --- | --- | --- |
| Seven distinct alpha0 forks | Ordinary/image prefix, tau, response0, fixed received oracle and common S | The one mixed equation above |
| Three distinct tau forks, each with its seven-alpha certificate | Ordinary functional/scalar, gamma/chord/interpolant, and **the same Q** | Degree-two image polynomial is zero: E1=E2=ordinaryPrior=0 |
| Four distinct kappa forks, each with the three-tau collection | Four original weights/claims, inactive scalar, gamma/chord/interpolant, and **the same Q** | Degree-three shifted row polynomial is zero: all four row errors vanish |

The three-tau step is now separately proved; the four-kappa step remains a
further obligation. Neither is a consequence of a single-tau equation alone.
Merely naming Q in every branch does not prove it is the same vector. Here
the same received oracle and common S with more than 255 fibres let
`common_support_identifies` retain the originally constructed Q for all later
final branches. More general overlaps may also suffice, but require a proved
intersection bound.

This elementary construction uses `7*3*4 = 84` alpha branches per fixed gamma.
It still does not recover individual components from their gamma batch.
Original reconstruction, component claims, semantic/copy challenges and the
payment/context/settlement endpoint remain to be connected.

## Literal causal boundaries

1. Fix C1 at its existing early commitment boundary. Its optional early
   identification is a classifier, not the only admissible extracted witness.
   C2 may depend on lambda/chi, but is fixed before both OOD points. Preserve
   the actual sequential OOD-answer absorptions.
2. Before gamma, fix both component-OOD vectors and the ordinary point claims.
   The received batch and virtual quotient may depend on gamma. At this
   boundary they do **not** depend on kappa or tau: evaluating them later in
   `prepare` does not add a mathematical dependence on those challenges.
3. Before kappa, freeze the inactive scalar as well as the four original row
   functionals/claims. Before tau, freeze the derived ordinary functional and
   affine-corrected scalar. The optimized `structured_weights.rs` path binds
   its canonical `AV8/functional/three-MLE-grouped64/chord/v2` description,
   scalar and `aspis-v8-image-gate-compact-functional-v2` framing before tau;
   this is not the older dense 16,384-byte functional hash. Retain the carried
   image weights, rather than a late final256-only membership test.
4. Before alpha0, fix the six serialized response0 fields and the actual
   fold nonce. The inspected research callback absorbs fields `[417..423]`,
   reconstructs c4, absorbs the round, and absorbs nonce bytes `[8..16]` before
   sampling alpha0. Changing that nonce creates a different pre-alpha prefix;
   it is not a replay of one frozen response boundary.
5. Each final256 may depend on alpha0. Freeze it and query-nonce bytes
   `[16..24]` before rewinding the query boundary. Retain the original ordered
   queries in the rho polynomial. Sorting an authentication frontier does
   not sort the scalar batch.
6. Rho follows the queries. Later compact responses may depend on every prior
   challenge, but precede their own fresh challenge. A Fiat-Shamir restoration
   must reproduce the output/advance state pair and every relevant cached
   query, not merely replace one nominal field value.

The literal carried prior is available to a mathematical extractor from the
public functional, first response and disclosed final256. It can check zero
directly. It must not infer that property merely from scalar acceptance.
Likewise, it must explicitly recompute each opened pointwise residual and
reject/record zero denominators. No probability is assigned to a source
correspondence gap.

## Access and resource contract

A single q22 proof exposes only 22 distinct fibres, not the common set S.
Under a collector which obtains each branch's support from that branch's
own q22 proof openings, at least `ceil(257/22) = 12` query schedules are needed
even to supply enough distinct positions. This is a cardinality-only minimum:
it guarantees neither acceptance, distinct collected positions, common support,
coherent finals nor completion within a cap. Under that collector, 84 branches
require at least 1,008 completed query-schedule continuations. This is not an
universal lower bound for every extractor: authenticated leaf data can be
reused across branches with proved identical commitments and derived oracle
inputs, but that reuse needs its own provenance and resource accounting.

Declare finite caps separately for prefix restorations, fresh challenge draws,
prover calls, accepted continuations, shared hash queries, and total transition
fuel. Record duplicate challenges, missing responses, aborts, query-parser
failures, denominator rejection, cached/advance mismatches and changed frozen
prefixes. Failed attempts consume these caps. A successful deterministic
certificate does not prove that a causal prover supplies it often enough.

| Access model | What it supplies | Not supplied for free |
| --- | --- | --- |
| Full fixed-word oracle | Values at explicitly requested indices | Merkle authentication or actual replay provenance |
| Authenticated reconstruction | Canonical root-bound leaves and their indices; possible cross-fork reuse under commitment identity | A method to elicit enough leaves or a shared support |
| Actual bounded replay extractor | Restored executions and their logged outputs/advances/failures | Fresh independent laws after arbitrary FS selection, or guaranteed success |

Seven, three and four are **distinct** challenge counts. Sampling enough
distinct useful forks, and preserving a common support through them, needs a
separate probability/runtime analysis. No honest-prover search or grinding
multiplier contributes security bits. The local 40,282-byte proof is not
extended by these analysis/replay openings, but the extractor pays for them.

Once four coherent final vectors are available, a possible executable
reconstruction applies one four-by-four Vandermonde inverse coefficientwise
to their disclosed 256-coefficient vectors. The actual natural lane/interleave
mapping must follow the existing fold theorem. This does not treat LDE
evaluations as message coefficients. The current code-submodule existence
proof is not itself a tested bounded interpolation implementation; common
authenticated support and useful-fork collection remain the harder access
obligations.

For the straightforward dense four-by-four application, the arithmetic model
is `256*16 = 4,096` K multiplications and `256*12 = 3,072` K additions, plus
matrix preparation. The output stores 1,024 K coefficients (16,384 bytes in
the selected 16-byte representation); this is output storage, not a measured
peak-memory bound including inputs and scratch. These are modeled operation
counts, not executed or formally cost-certified instructions/CU. The
interpolation and fork bookkeeping are private extractor work: neither the
seven-alpha nor three-tau certificate adds a public message or proof-body
value, and no new full-view privacy theorem follows from them.

## Total accepted-extraction accounting

Let A be acceptance by the intended complete repaired verifier. Define X only
when a declared resource-bounded extractor actually returns a witness passing
the literal payment, authoritative context and settlement validator. Either an
early candidate or a later fork-recovered candidate may establish X. In
particular, failure to bind every claim to the first high-agreement C1 candidate
is not by itself `not X`.

For a specified implementation of this proposed extractor, assign a unique
terminal reason by first-failure precedence. The desired disjoint accounting is

```
A AND NOT X
  = accepted terminal authentication/source failure
    OR accepted terminal replay/resource failure
    OR accepted terminal insufficient/coherence-failed fork data
    OR accepted terminal reconstruction/component failure
    OR accepted terminal semantic/context/validator failure.
```

This is a contract for the extractor state machine, **not a proved partition
of an already implemented extractor**. Each label must be tied to its actual
return/abort path before assigning a bound. `earlyC1 = none`, a failed early
candidate, provider `none`, and radius failure may continue into the fork
fallback; they are not automatically terminal failures. Scalar acceptance
with nonzero prior or failed pointwise checks remains visible and consumes
the relevant rho/later-round collision or replay budget. Replay failures
cannot all be renamed one pre-query event.

The near/far classifier can be applied inside each terminal class, but cannot
replace X. `RelationCompatibleMoment` charges rho and three later repairs for
the event it actually averages. The prior near-region ceiling already contains
such terms. Use a common event partition or event-weighted collision bounds
to charge them once; do not mechanically subtract them from an old subtotal.

## Upstream degrees and surviving controls

On the genuine C1 own-support the received batch is
`Encode(C1batch(gamma)) + gamma^26*(H + gamma*G + gamma^2*D)`.
The helper word curve is degree two, with no helper-codeword premise. Outside
that support C1 is still arbitrary. False low-lane claims retain
`gamma^-26*c1Error(gamma)` after normalization; after reconstructing a fixed
full tuple, the total claim-error polynomial has degree at most 28. Neither
the helper reduction nor the seven-alpha certificate deletes those errors or
moves a tuple backward across lambda/chi.

Keep the two-codeword minority control separate from a payment attack: a
high-agreement early candidate p and a lower-support alternative p' can be
different, while the supplied claims and relation may be consistent with the
alternative codeword/reference p'. A polynomial reference is not itself a
checked payment witness; no same-execution valid-payment fixture is asserted
for this control. The exact q22 all-minority query factor for 16,535 fibres is
`choose(16535,22)/choose(262144,22)`, approximately `2^-87.727713`.
This is a conditional query-only diagnostic, neither complete acceptance nor
a forgery. Its role is to test the extractor's candidate classification
instead of trying to prove that every accepted claim must identify the
majority candidate.

The adaptive-prior-zero control remains: adjusting a final coefficient can
make the prior zero while changing query agreement. Thus seven accepted forks
without common-support coherence are insufficient. The T512 invalid-image
case and zero-fold/nonzero-image kernel remain: one tau equation or final256
alone cannot certify the quotient's image. Original/paired root products,
high-J own-support recovery, shifted-batch cancellation and later repairs
must also remain in any final extraction experiment.

## Reuse map and source boundaries

| Existing artifact | Exact reusable content | Boundary |
| --- | --- | --- |
| `ExactFoldRecovery`, `PartialFoldRecovery.four_support_folds_recover` | Code-valued interpolation in alpha and reconstruction of actual four slots on a common support | Mathematical support and values; no authenticated access algorithm |
| `PartialFoldSelected`, `ExactFoldSelected`, `SelectedReceivedOracle` | Selected encoder/lift equality, canonical inverse schedule, stored-point bijection and actual residual sign/order | Field/source-shaped model, not translated packed Rust query path |
| V7 `V7Tag73ExactOneFoldEncoderBinding`, `V7Tag73CanonicalOneFoldSchedule`, `V7ExactOneFoldDomains` | The unchanged natural-circle and final-line evaluation conventions and exact domains | No V7 q16, old raw-consistency, work or recovery-loss law imported |
| `EarlyC1Identification.matching_set_cap` / V7 subfield/overlap work | Full-code overlap at most 256 complete fibres; possible own-support descent bridge | Does not select the proper payment witness by itself |
| `FirstImageDiscrepancy`, `OptimizedRelationRefinement` | Actual six-field compact grammar, degree-six error and boundary/mixed-image identity | Seven roots require one coherent reconstructed Q |
| `ShiftedRowPrefix`, `ClaimTransport`, `OODInterpolantRows` | Shifted four rows, degree-three errors, actual chord/interpolant affine correction | Separate kappa/tau collections must use the same Q and frozen inputs |
| V7 `Pool/V7MerkleQueryExtractor` | Exact C1/C2 typed leaf/node preimages and explicit failure taxonomy, shared log principles | Its `Fin16` disclosed-proof endpoint is not q22; actual V8 collector needs a new instantiation |
| V7 `K1/V7Tag73AtomicForkUniformScheduler` | Causal actor-tagged oracle machine, explicit output/advance pairs, fuel/call caps and failure padding | Not a V8 seven-alpha/three-tau/four-kappa success theorem |
| V7 `K1/V7Tag73RestoredQueryBatchForkController` | Prefix-before-answer restoration/controller pattern | Its q16/work/profile-specific routes and numerical resource envelope cannot be transplanted unchanged |

The V7 files above were inspected at immutable source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, not taken from advancing main.
No old recovery bound, 100-target union, `inactiveExact` acceptance premise,
or compiler/refinement equality is assumed here.

The inspected research source SHA256 values were:

| File | SHA256 |
| --- | --- |
| `experiments/structured_weights.rs` | `06befd20c084234ce1afa2d7cf3612a12370fdb0e98e95db30d89cf245b51089` |
| `experiments/relation_callback.rs` | `285c90695cc7558a88ffc7cb50de4235b68c7ceed9d0600d5cc9ba7f682607ed` |
| `experiments/inactive_row_binding.rs` | `4642f1e4361aeb9f991ef917f8efdea292187fe3de9e3a9d351230859f9ad98b` |

## Stopping point

| Certificate / evidence | Exit | Wall | Peak RSS (bytes) | Swaps | Audits |
| --- | ---: | ---: | ---: | ---: | --- |
| [SevenAlpha v1](experiments/seven-alpha-recovery-v1.log) | 0 | 49.27 s | 4,799,414,272 | 0 | Six, standard-only |
| [ThreeTau v1](experiments/three-tau-recovery-v1.log) | 0 | 49.07 s | 5,281,333,248 | 0 | Two, standard-only |

SevenAlpha source/olean SHA256:
`c36bd88630d0529bfd330b5341b6763c5db8859cc7e7b91538bbd04717f3ad21` /
`cbf44c42d7d85eba1bb3e60142a194368f7d919e8512e6a4f3afbff351390b1c`.
ThreeTau source/olean SHA256:
`79dbb8de3b097d6af59c072c2ce0fb11e88e42a8dc9c42e2336c6f274ad113b5` /
`2bf2cb616f3a88396eacc6fb1fb31ece5c2f2e4ff2397dcf199a53dc0bb6e25d`.
The proof agent ran these cached focused leaves serially under the existing
7-GiB guard; this documentation review ran neither. Standard-only means no
dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`.
Both runs completed their provenance postflight; see the focused
[seven-alpha review](seven-alpha-recovery-review.md) and
[three-tau review](three-tau-recovery-review.md).

The completed endpoint is deterministic quotient recovery and image/ordinary
separation from a qualifying **fixed-word common-support fork grid**. The next
bounded step is executable four-disclosure interpolation plus an explicit
collector/coherence experiment on the minority-codeword control. The
four-kappa composition, authenticated/private replay access, production
witness, efficient global extractor, resource-bounded FS theorem, full-view ZK
and matched complete-transaction CU remain open. This document changes no
source, proof bytes, protocol messages, production branch, or deployment state.
