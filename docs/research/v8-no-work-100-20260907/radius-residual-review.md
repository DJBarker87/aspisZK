# Beyond the near-anchor regime: radius is not extraction failure

Date: 2026-09-08. Base/checkpoint resolved to
`954b88948ba7a4aab809ec6d21e3524af033f148`, on
`research/v8-no-work-100-20260907`. The worktree was clean at the start;
no reset or main edit. Downloaded work order: `CODEX_NEXT.md`, SHA-256
`0ac8e8aa831e2bb35aeb946cde4be54a203051d54481d607b2187f2c8f2d03b0`.

## Decision

Do **not** try to bound all accepted executions outside radius 9,301 by a
cryptographically small probability. That classifier can discard a uniquely
recoverable codeword. The repaired research relation suffix concretely accepts
the boundary fixture when its fresh queries miss the corruption. This is not
a payment forgery, nor a completed full-payment embedding.

This continuation contributes two useful endpoints beyond that obstruction:

1. A kernel-checked scalar-power/affine-transport interface derives the repaired
   ordinary discrepancy from component claims, including its nonzero degree-28
   error polynomial. It does not assume `inactiveExact` or the desired discrepancy.
2. An executable decoder reads recovered C1 message cells, reconstructs a
   literal transfer witness and checks it with the existing payment compiler,
   authenticated runtime context, spent-nullifier context and exact settlement
   transition. The previous unnamed tuple-to-witness task now has a concrete
   checked endpoint and a precise missing coverage implication.

There is still **no bound for all accepted residual extraction failures**.
QM31 q22 remains a research priority, not a validated 100-bit design. The
near theorem is consumed unchanged, not replayed or relabelled global security.
The proof body remains 40,282 bytes. This continuation changes no verifier
grammar and supplies no new full-transaction CU or privacy result.

## 1. Radius boundary: theorem and actual source-shaped experiment

[RadiusBoundary.lean](experiments/RadiusBoundary.lean) proves symbolically, for
an arbitrary finite domain and code with pairwise overlap at most delta:

- if received r differs from anchor a at at most s positions, every distinct
  codeword b has distance at least T-s-delta from r;
- if distance(r,a)=s exceeds cutoff and cutoff+s+delta<T, no codeword is
  inside cutoff;
- if 2s+delta<T, a is strictly nearer than every distinct codeword.

For T=262,144, s=9,302, delta=256, the other-codeword distance is at least
252,586, while a is still the unique nearest codeword **if a belongs to the
code**. The theorem states comparisons and does not manufacture membership.
The cutoff failure is not loss of mathematical recoverability. This also
does not provide a fast decoder: exhaustive nearest-codeword search would be
a finite but unacceptable extractor.

The exact fresh-query diagnostic is

```
choose(252842,22)/choose(262144,22)
= 0.451637932155366864854413252653196058980656793131013825813704...
```

[The ledger script](experiments/radius_ledger.py) checks the binomial rational
against an independent product of 22 rational factors. This is the probability
of missing all changed fibres, not a full verifier acceptance upper bound.

### Code and indexing applicability

The previous `NearGammaFibreBridge.full_fibre_overlap_le_256` proves the cap
for the **original** exact encoder, using the injective fibre-major map
`(f,s) -> 4*f+s` and the 1,024-symbol overlap theorem. Its generic
`fibre_overlap_le_256` can be used once a quotient symbol cap is established.
The new geometry theorem accepts that cap explicitly. A translated identification
of the actual natural quotient space, its evaluation map and this original
encoder is **not** claimed completed here. Merely having a 1,024-entry vector
does not discharge it.

The executable fixture uses the actual four slots
`(x,y),(x,-y),(-x,-y),(-x,y)`, actual packed openings and
`qm31_circle_to_line_fold4`. Its virtual word is
`R_gamma=(sum gamma^lane*v_lane-I)/L`; matching means equality between its
actual fold and evaluation of the disclosed final256. No V7 raw-word
`consistencySet` has been substituted.

### Causal embedding achieved: relation suffix, not full payment

[radius_boundary.rs](experiments/radius_boundary.rs) extends only research
fixture visibility and adds a separate cfg entrypoint. The verifier receives
canonical proof bytes, not witness-side quotient coefficients.

- C1 is a precommitted canonical T2(x) word in lane 0; the other C1 lanes
  are zero. This is a codeword diagnostic, **not a valid payment trace**.
- C2 is precommitted H=G=0 and D=1 on all four slots of exactly fibres
  0 through 9,301, zero elsewhere. The commitment is fixed before OOD
  (indeed independent of earlier lambda/chi, which is an allowed special case).
- The three point rows, inactive value and sequential OOD vectors honestly
  describe the T2/zero component tuple. OOD vector 0 is absorbed before
  point 1 is sampled; both vectors precede gamma.
- Thus the received virtual quotient differs from the honest image-valid Q0
  by gamma^28/L on exactly those fibres. Every one of their four chord
  denominators is checked nonzero. No word is chosen retrospectively after OOD.
- `prepare(..., true)` uses shifted row scales, freezes the ordinary scalar
  and weights, then samples nonzero tau. Both image claims of Q0 are zero.
  Response0 precedes alpha0; final256 is the true fold. Queries precede rho;
  each later compact response precedes its next challenge.
- Both real Merkle frontiers, canonical fields and all four compact relation
  responses are checked by `inactive_binding::relation`. Fixed nonces are
  zero; no seeds are retried or selected for acceptance.

For fixed seeds 1..32, **14 relation suffixes accepted**. These were exactly
the 14 schedules missing all corruption. The other 18 had nonzero folded
residuals and rejected in this run. This is deterministic host evidence,
not a sampling certificate. Rare folded/rho/later-round collisions remain
legal; the test does not assert their universal absence.

Four additional fixed false-D-row controls check the concrete identity

```
prepared_claim - dot(prepared_ordinary_weights,Q0)
  = kappa * gamma^28 * row0_D_error.
```

All four rejected in this run. This tests the shifted coefficient/sign in the
actual research preparation rather than an independently assumed prior.

The semantic sumcheck prefix is **opaque** in this fixture. It does not run a
valid-payment semantic producer or the full deployment/account preamble.
Consequently the requested full valid-witness/corrupted-commitment embedding
is unfinished. The separate genuine witness fixture below is not the same
proof and must not be spliced into it in the argument. What is conclusively
refuted is a tiny no-anchor bound inferred from this relation suffix alone.

## 2. Causal search: optimize strategies, not favourable transcripts

[radius_strategy.rs](experiments/radius_strategy.rs) performs exact backward
induction in an explicitly restricted F11, T=8, q=2 game. Two corrupt fibres
are fixed before alpha; their folded noise is 1+alpha*(x+1). This is an
abstract invertible four-slot model, **not** the actual Aspis circle domain.

The first response has six freely chosen coefficients, with the actual
compact constraint 4*(c0+c4)=prior. All 11^6 replies for each of 11 priors
are enumerated. For each revealed alpha and resulting prior, the prover
chooses any affine final f0+f1*x **before** the fresh uniform distinct query
pair. Query batching is prior-rho*(r0+rho*r1), rho nonzero. Three subsequent
compact responses may adapt to all previous information.

Exhaustion finds the attainable six-root maximum for a nonzero-prior compact
degree-six discrepancy. Scaling by a nonzero prior bijects the response
spaces. A zero prior can remain zero. Hence optimal three-round repair
probability is exactly 1-(5/11)^3 = 1206/1331. Dynamic programming uses this
continuation value rather than pretending later replies were fixed early.
The first-response maximization sums over alpha before taking its maximum.

Four fixed component-error families are included. Gamma is nonzero; D noise
scales by gamma^28. For each gamma the inactive scalar is chosen optimally
**before kappa**. Row powers are 1,kappa,kappa^2,kappa^3. Nonzero-noise scaling
bijects final, residual and compact-discrepancy strategies, justifying the
normalization. Tau can be revealed before response0: this restricted
image-valid/low-support subspace pairs to zero with the carried image vector,
so its optimum is unchanged for each tau. This does not test image-invalid
targets or pretend image constraints are unnecessary outside the subspace.

The exact suffix optimum for prior zero is 3936855/4099480. The four
gamma/row family numerators are
393685500, 388249250, 388866500, 389152000, over 409948000.
The selected maximizing final is nonzero in 110 conditional states; this
does not assert strict improvement over zero in every such state (ties are
possible). See the complete [output](evidence/radius-strategy-host.log).

This is exhaustive over responses and affine-final strategies **within the
specified game**, not all committed oracles, image classes or payment
strategies. Its high small-field repair rates have no QM31 extrapolation.
It establishes an executable causal test framework for proposed residual
lemmas, not a new full-parameter upper bound. An additional exhaustive
312,500 F5 constant-code distance comparisons and a degree-q two-root
shifted-batch case serve as small arithmetic regressions.

## 3. New deterministic bridge: derive the claim error

[ClaimTransport.lean](experiments/ClaimTransport.lean) supplies the following
kernel-checked interfaces over an arbitrary field and linear spaces:

| Theorem | Actual conclusion | Still needed for selected source |
|---|---|---|
| component_error_eval/coeff/degree/nonzero | Scalar-power batch error is a polynomial of degree <=28; one wrong component makes it nonzero | Concrete point functionals and C1/C2 timing |
| corrected_prepare_discrepancy | For reconstructed U=L(Q)+I, the transported ordinary discrepancy is inactive error + kappa*row0 error + kappa²*row1 error + kappa³*row2 error | Concrete chord multiplication/transpose and encoder port |
| batched_prepare_discrepancy | The latter row errors are evaluations of the derived component-error polynomials | Couple recovered pre-gamma tuple to actual claims |

L is a constructed linear-map input and the covector transport is literally
composition with L. The theorem does not ask for the discrepancy equality
as a premise. It permits any inactive discrepancy, including one selected
after gamma and before kappa. It neither freezes a late tuple before
lambda/chi nor proves that accepted executions have a component tuple.

These results remove an algebraic interface assumption once the concrete
maps are instantiated; they are not a Rust-to-Lean translation or a completed
`RowSeparatedImageGame` source constructor. The radius fixture's true/false
D controls differentially test the intended assembly in real QM31.

## 4. Concrete tuple-to-payment endpoint

[recovered_witness.rs](experiments/recovered_witness.rs) defines a deterministic
`decode` and `extract_checked`. The input is the recovered canonical
16-column semantic projection of C1 in the selected **message-table**
convention. The source `CircleEncoder::encode_c1_message` directly pads
and encodes these message coefficients; the decoder does not reinterpret
them as LDE evaluations or silently run an inverse FFT.

| Item recovered | Source cells / obligation |
|---|---|
| Owner/nullifier secret | Row 12, lanes 0..7 |
| Input amount and salt | Sponge blocks 1..3; amount row44 and salt row44/60 |
| Recipient and change note openings | Sponge blocks27..29 and30..32 |
| Pair selection/occupancy | Source path level0 ordered children; occupancy auxiliary row1017 |
| Membership and forest path | Source path row function, 20 sibling/index bits plus 3 super-root steps |
| Public value/asset/note/nullifier claims | Existing transfer compiler validation, not assumed from the decoded type |
| Pool/deployment/retained anchor | Explicit comparison against caller-supplied authenticated runtime binding |
| Nullifier freshness and settlement | Caller spent-nullifier context; compiler result must equal the supplied complete late transition |

The outer runtime-root equality is checked **before** the forest compiler
substitutes its temporary lane-root context. The fixture constructs a valid
1000 -> 600+400 transfer and its current live snapshot, compiles C1, then
passes **only C1 plus public/context/transition inputs** to extraction.
It does not pass the original witness to the decoder. Literal equality
with that witness is a test assertion after extraction.

The implementation scans 16*1024 cells for canonical shape, reads a fixed
number of selected cells/path bits, constructs one witness and calls one
fixed-size compiler/validator. It uses no oracle, search or retries. The
benchmark performs 100 checked extractions. This is a bounded executable
**endpoint given coefficients**, not an executable full proof extractor.

All 18,089 raw compiled trace residuals are zero on the unmasked fixture.
Fourteen mutations reject, covering witness limbs, values, directions,
path, canonicality/shape, asset, transition, spent nullifier, deployment and
the authoritative outer anchor. Populating all 3,803 source-listed
relation-free mask cells preserves the decoded witness and all non-padding
residual classes in one assignment.

Important test correction: the host residual inventory explicitly includes
3,803 **zero-padding** residuals. Therefore asserting its entire
`all_zero()` on a populated mask assignment was false. The retained test
checks those padding residuals are nonzero, then separately checks every
other class. This is not a ZK theorem and is not permission to erase a
verifier check. It separates raw trace normal form from witness extraction.

### Remaining tuple-to-witness obligations

1. Original-code recovery and C1 descent on own support: prior mathematical
   results exist; no source algorithm is obtained by noncomputable tuple choice.
2. C1 must be recoverable with the correct **pre-lambda/chi** causality.
   A full tuple chosen after adaptive C2 but before gamma does not provide it.
3. Correct component point claims must imply the selected semantic/copy
   constraints with their actual masks, H and public statement. The new
   transport algebra handles none of the earlier challenge conditioning.
4. Universal selected-residuals-to-`extract_checked` success remains open.
   A successful validation call guarantees a checked returned witness in the
   tested Rust path; it does not guarantee the decoder succeeds on all
   accepting traces. The earlier formal deterministic witness results use
   older statement/column interfaces and are not this port.
5. Withdrawal/fee-specific extraction, full source correspondence, replay
   runtime and FS extraction success remain open. No withdrawal result is
   inferred from the transfer fixture.

## 5. Correct residual event and total accounting

Let A be acceptance by the intended repaired **complete ideal verifier**,
not merely the implemented suffix. Let X mean an extractor returns a
witness that passes the literal payment/context/transition validator within
declared resources. Only the coefficient-to-witness part of X is implemented
here. There is no fully source-connected, resource-bounded V8 recovery
algorithm in this continuation; assigning one an invented runtime would
hide the main obligation.

Define N after the OOD/gamma quotient prefix as existence of an
image-valid quotient anchor within 9,301 fibres. Define T at extraction
completion as availability of a recovered, descended canonical component
tuple. Neither N nor T means X. The disjoint accounting identity proved in
`failure_partition` is:

```
A AND NOT X
  = (A AND NOT X AND N)
    OR (A AND NOT X AND NOT N AND NOT T)
    OR (A AND NOT X AND NOT N AND T).
```

The first class must itself split into the **specific bad-binding event**
bounded by the near theorem and near cases with correct binding but no
checked witness. Its entire mass is not 2^-105.145. In particular, do not
replace the other two classes by A AND NOT N, or charge successful
out-of-radius extraction as failure. This propositional identity is just
bookkeeping; the new content is the radius obstruction and checked endpoint.

Apply the following precedence to real execution logs before any mathematical
near/far classification. These are proof obligations, not a newly ported
total V8 classifier:

| Ordered outcome | Observable when | Treatment if original execution accepted |
|---|---|---|
| Authentication/source disagreement | Parsing/opening/refinement | Separate coupling/binding obligation; not an anchor event |
| Replay abort, exhausted fuel, missing response | Replay execution | Keep accepted mass; no automatic zero bound |
| Restored/cached/advance or gamma/alpha mismatch | Correspondence/replay boundary | Keep separately; no fresh-law assumption through mismatch |
| K13 ideal rejection / scalar acceptance without pointwise acceptance | Queries/rho and later rounds | Charge correct joint batch/repair event only after source implication |
| K13 query, fold, list classes | Their actual prefix plus query observation | Preserve classes; old q16 raw-word definitions not a q22 quotient proof |
| K14 width29/provider none | Ideal prefix/classifier or actual provider call | Do not equate all none with N-complement; own-support recovery may still work |
| Tuple found, descent/point/semantic/decoder validation fails | Respective checks/extraction | Count as unrecovered; classify concrete reason |
| Checked witness returned within budget | Extractor completion | X, regardless of radius; contributes nothing to A AND NOT X |

This carries forward the source inventory in [adaptive-tail-review.md](adaptive-tail-review.md).
The actual K13/K14 source-to-V8 quotient partition remains missing. This
continuation does not claim the table is an implemented source classifier.

### Regression placement

- Original J=9557 and paired J=9556 root products: far/coverage obligations
  remain; their disproved same-support shortcuts are never reused.
- High-J J=252843: consume near-gamma own-support coverage; additional
  combined-zero fibres need not match componentwise. Correct binding still
  must lead to a checked witness.
- T512 invalid-image exact quotient: retain the existing joint image theorem,
  jointly with relation repairs. No query-only or final-only substitute.
- Zero-fold/nonzero-image kernel: retained, no final256 image certificate.
- Unshifted cancellation and late-inactive timing falsifier: shifted powers
  and fresh kappa remain; do not add inactiveExact.
- Shifted degree-q batch and later repairs: preserved both in source fixtures
  and reduced strategy space; rare challenge acceptance is allowed.
- New s=9302 boundary: N is false under the code hypotheses, but a unique
  nearest anchor survives. Suffix acceptance is measured; full X-linked
  proof embedding remains unfinished.

## 6. Ledger, timing and costs

[Machine-readable ledger](radius-results.json) consumes the prior exact
near result by content hash. Unsupported quantities remain null/symbolic.

| Event/interface | Fixing prefix / fresh randomness | Bound or status |
|---|---|---|
| Existing supported near bad-binding event | Pre-gamma tuple; later causal kappa/alpha/query/rho | Reuse 53/(k-1)+24/k+choose(9556,22)/choose(262144,22) |
| Boundary queries miss fixed changed support | Full final/word prefix; fresh uniform distinct queries | Exact 0.451637932155... diagnostic, not failure bound |
| Component-error polynomial interface | Constructed tuple and component claims before gamma | New degree<=28/nonzero identity; no new independently added loss |
| Accepted residual recovery failure | Depends on complete extractor outcome | No quantitative upper bound |
| Correctly bound tuple but failed checked witness | Earlier semantic/copy and actual coefficient recovery | Endpoint executable; coverage bound missing |
| Authentication / FS / replay / privacy | Their own actual experiments | Not quantified by this continuation |

The existing 24/k already includes four relation repairs. The new transport
lemma is an interface, not another event to add. An expression such as
`E_near + Pr[A AND NOT X AND NOT B_near]` is justified only after coupling
A to that exact supported event; the second term is still missing.
There is no numerical global remaining allowance. The old 396430 inventory
is not imported. Primitive/source hypotheses are not assigned tiny invented
probabilities. No PoW credit or quantum-security claim is made.

The unchanged maximum census is:

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

No values, nonces, padding or rounds were added. The observed maximum of the
32 fixture bodies is 40,022, which is **not** the protocol maximum.
The classifier/extractor repair proposed here costs zero transmitted bytes
and zero verifier operations; its missing general decoding algorithm has
unmeasured extractor cost. It is not a paid-by-grinding security repair.

Inherited dense transpose and the 16,384-byte public-weight transcript
absorption remain real research costs. The source fixture used about 34 MB
RSS; this is not full-prover RAM. No full prover, search benchmark, SBF frame
measurement, complete transaction, disk/network throughput or new deployment
was run. q23/41,527 and quintic q22/42,984 remain unapproved controls.

## 7. Evidence and next stopping test

[Evidence manifest](radius-evidence.json) records commands, source hashes,
exit codes, wall/RSS/swap and axiom output. Both new Lean leaves use the
pinned Mathlib cache, not changed Aspis oleans from concurrent main work.
All retained declarations use only propext/Classical.choice/Quot.sound;
no new axiom or sorry. Local proof errors were corrected before the focused
recheck, not escalated into a package build. No seven-leaf near replay.

Measured successful runs on Apple M3 / Rust 1.93 / Lean 4.32:

| Target | Wall | Peak RSS bytes | Scope |
|---|---:|---:|---|
| RadiusBoundary.lean | 3.31 s | 2,826,108,928 | Generic geometry/partition |
| ClaimTransport.lean | 3.01 s | 2,834,694,144 | Scalar-power/transport algebra |
| radius strategy binary | 0.53 s | 1,572,864 | Exact reduced strategies |
| radius relation fixture | 6.06 s | 33,931,264 | 32 seeds + 4 controls |
| recovered witness binary | 0.34 s | 3,178,496 | Transfer endpoint/mutations |

All exited zero with zero recorded swaps. The 100 extraction calls took
0.050673917 s in the last run; this is an aggregate host timing, no tail
guarantee or verifier CU claim.

**Next decisive bounded experiment:** connect a genuine selected
payment-semantic producer to the s=9302 committed-component fixture and
recover its C1 through an explicit V8-compatible decoder, then run the
checked endpoint. Stop that experiment if the decoded C1 depends
illegitimately on lambda/chi, if the verifier requires a previously omitted
semantic/copy discrepancy, or if the decoder cannot be bounded. Record the
first concrete obstruction. Success would demonstrate an X-backed
out-of-radius branch and justify an extraction-based residual partition;
it would not alone bound all remaining malicious oracles.

The strongest mathematical follow-up is therefore **recoverable C1 plus
semantic correctness across radius strata**, not an upper bound on the
bare no-anchor event. The present grammar remains plausible but unvalidated.
This run closes meaningful algebraic and executable substeps, not the
global recovery/FS/ZK/CU contract.
