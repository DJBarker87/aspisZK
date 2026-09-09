# Geometric anchors in the same causal relation execution

Continuation of `bbca32e0e30be2c489c6437dd670da164e6d852f` on the existing
research branch. Production, the verifier implementation, the opt-in profile,
transcript framing and the **40,282-byte** maximum body are unchanged.

## What this continuation connects

The new endpoint is `PreAnchorJoint.geometric_joint_dichotomy`. It combines
the selected circle-code geometry with the carried image/shifted-row game,
using **the same arbitrary received quotient word** for geometry and actual
query residuals. It does not assume an anchor supplied by a provider, an
exact polynomial received word, or a final fixed before its real choice time.

The final checked-source and resource evidence is recorded in
[pre-anchor-joint-evidence.json](pre-anchor-joint-evidence.json). A successful
log matching the current source is required by its reproducible audit; failed
diagnostic logs are not proof evidence.

Fix the indexed received virtual quotient `R : Fin 1048576 -> QM31`, a radius
`B`, and the alpha challenge set `A`, before kappa and tau. Let an alpha be
eligible when some final256 codeword differs from the actual normalized fold
of R on at most B final positions. For `5B+255 < 262144`, exactly the following
case split suffices:

- **Sparse:** at most three eligible alphas. Any causal strategy's accepted
  B-close-final event has probability at most `3/|A|`, however it chooses its
  responses and final after the earlier challenges.
- **Dense:** geometry constructs one full quotient-code coefficient vector
  Q within `4B` complete fibres of R. That same Q represents **every** B-close
  final at every alpha, including finals chosen after kappa/tau/alpha.
  On the event that this Q has an invalid image or a wrong ordinary row,
  accepted B-close finals have probability at most
  `(q+3)/|G| + 24/|A|`, where G is the nonzero challenge set.

The dense Q is quantified **before the rows and the entire strategy** in the
endpoint. It uses the received-word geometry, not a chosen accepting branch.
The endpoint also retains `eligible.card > 3` in its dense branch, making
the sparse/dense prefix partition explicitly disjoint in the checked statement.
Existence remains mathematical; this is not an efficient enumeration of QM31,
an implemented decoder, or a resource-bounded rewind extractor.

The reason one Q represents all close finals is concrete. Four eligible
folds reconstruct Q outside at most 4B fibres, using the existing symbolic
interpolation theorem. Any other B-close final agrees with the encoded fold
of Q at more than 255 positions outside their union of bad supports. The
selected final code's literal degree/overlap theorem forces equality of its
coefficients. No list-membership hypothesis or 100-target union is used.

At `B=2325`, Q is within **9300** complete fibres, inside the previous 9301
near-anchor radius. This is the chosen useful connection, not a new proof-size
or query parameter. At larger B the theorem's 4B radius must still be charged;
it cannot be called the old near-gamma regime automatically.

## Why this is one game rather than two compatible examples

`SelectedReceivedOracle` constructs the field-domain oracle from R using the
stored final-coordinate bijection and the selected child/slot indices. Its
canonical inverse2x/inverse2y tables are proved equal to the field inverses.
Its normalized fold is exactly the fold in the selected geometry theorem;
its residual is exactly `finalEvaluation - foldedReceived`, in query order.
The support parameter of the old oracle type is explicitly `D=D`, so its
support premise is vacuous, not a hidden exact-polynomial assertion.

Q is an analysis object, not a public message. The separate
`ReferenceIndependentRelation` leaf proves that replacing Q leaves actual
weights, claims, received values, response grammar and terminal acceptance
unchanged. It proves probability equality by removing only the dependent
discrepancy-index transport. The **event predicate is held fixed** during
that proof. The final endpoint first chooses Q and defines its bad event,
then transports that identical event back to the original execution.

`RepresentedImageGame` handles the supported event within the original
averages, not by conditioning the challenge law on successful recovery.
Once a represented final is fixed, a nonzero carried error remains the
constant coefficient of the shifted rho polynomial, even if all query
residuals are zero. Its degree is q. Sequential degree-six repair bounds
charge the first and three later relation rounds once each. The original
complete compact field-game constructors derive the discrepancy, degree,
same-prior and terminal-zero interfaces; the new endpoint does not assume
those equalities as unverified correspondence premises.

## Exact event ledger and remaining mass

For ideal fresh full-field alpha challenges and nonzero kappa/tau/rho,
`k=(2^31-1)^4` and q22:

| Event, restricted as above | Exact ceiling | Scope |
|---|---|---|
| Sparse geometry; accepted close final | `3/k` | All causal continuations on this event |
| Dense geometry; invalid-image Q; accepted close final | `24/(k-1)+24/k` | Image mixing, rho, four relation repairs |
| Dense geometry; invalid-image or wrong-row Q; accepted close final | `25/(k-1)+24/k` | Fixed image/row partition; uniform ceiling, not sum |

Each displayed ceiling is below `2^-118`. These are **local field-game event
bounds**, not a new global security level. The image-only and image-or-row
events overlap and are not added. The earlier 105.145190-bit near-gamma
bad-binding ceiling covers a different event; it is not subtracted from or
added to this table mechanically. No historical 396430 inventory is imported.
For display only, the three ceilings correspond respectively to
122.4150374966, 118.4150374966 and 118.3852901532 bits. The JSON stores their
exact rational numerators/denominators; integer comparisons certify the
displayed 118-bit inequality, not floating-point security estimation.

For the eventual target `Pr[complete acceptance AND checked extraction fails]`,
use this precedence:

| Class | Status |
|---|---|
| External source/authentication/replay mismatch, abort/fuel/missing response, cached/advance mismatch | Explicit separate obligations; not tiny invented probabilities |
| Faithful field game; sparse geometry; close final | New charged event |
| Faithful field game; dense geometry; close final; bad image/ordinary row | New charged event |
| Faithful field game; dense geometry; close final; correct image and rows | Component/C1 and checked payment-witness recovery still needed |
| Faithful field game; final farther than B, in either prefix class | Accepted **failed extraction** remains unbounded; radius failure alone is not failure |
| Any class in which the specified extractor returns a validated witness | Zero contribution to the target failure event |

This is a total classification of where the mass must go, not a proof that
all remaining classes are negligible. Provider `none` is not used to discard
executions. Scalar-only acceptance and later repairs remain inside the actual
field-game averages. The numerical global allowance remains **unknown**.

The mathematical source bridge begins after R is fixed. The selected source
absorbs both sequential OOD vectors and derives gamma before kappa. Its chord
and batched interpolant depend on those earlier values, although some are
computed after sampling kappa. That is supporting source inspection, not a
Rust-to-Lean proof of the prefix constructor. Early C1-before-lambda/chi
causality, actual authentication/replay resources and full Fiat–Shamir mapping
are still separate. Labels alone do not prove fresh conditional laws.

## Payment endpoint progress

[PositivePackBinding](positive-pack-binding-review.md) reuses the literal V7
QM31 packing formula. The selected old scalar lanes 92/93 are C1/public-asset
expressions, not lambda/chi/C2 expressions. On canonical base-valued Boolean
rows they cannot cancel the new residual in slot94. More strongly, at row1014
their selectors vanish by public structure, so the pack is exactly
`u*(recipient*change*inverse-1)`, even for arbitrary QM31 claims there.

Last-pack zero therefore forces the inverse equation. Last-pack zero is
**not assumed to follow from proof acceptance here**: the semantic/zerocheck
and concrete source connection must enforce it. An explicit off-domain
extension-field cancellation regression prevents misuse of the base-coordinate
result. No new residual, byte, mask change or verifier operation is added by
this continuation; it proves a property of the already opt-in control.

## Executed falsification controls

The optimized standalone Rust control uses seven actual non-axis F31 circle
fibres and the normalized four-slot fold. It exhausts 2187 fixed received
words in a declared ternary family, all 31 alpha values and all 31 constant
finals after each alpha. It finds 2084 sparse and 103 dense words; every one
of the 833 eligible dense continuations equals its geometric anchor's fold.
The maximum anchor distance is four, attained as expected.

The same control records a strict-gap counterexample with `T=5,B=1,cap=0`:
five cubic fibre words admit five one-error finals, but no cubic covers all
five chosen finals. Thus `T-5B>cap` cannot generically become equality.
It also reconstructs a legal compact discrepancy with nonzero boundary7 and
four distinct roots: four accepting alpha values do not establish an exact
image/relation identity. Probabilistic collisions remain legitimate.

This exhausts the stated finite family and adaptive constant finals, **not
all causal strategies**, full payments or the QM31 field. It is a falsifier
and implementation check, not experimental evidence for a 2^-118 event.
Compilation took0.81s/148,602,880B RSS; the control took0.45s/1,736,704B RSS,
both exit0 and zero swap on this Apple host. These are not prover/extractor
timings, SBF CU or new full-transaction measurements.

All older root-product, paired, high-J, invalid-image T512, zero-fold image,
row/query-cancellation and radius-boundary controls remain unchanged. No
general coverage is claimed by moving those cases behind a new predicate:
uncovered cases retain their previous explicit obligations. Own-support
recovery does not become the disproved same-support assertion.

## Reproduction, provenance and decision

All eight focused leaves passed with only the three standard axioms, exit0
and zero observed swaps. Peak RSS is recorded in bytes, not confused with
the smaller peak-footprint measurement reported separately by macOS:

| Leaf | Wall seconds | Peak RSS bytes |
|---|---:|---:|
| PreAnchorEligibility | 21.86 | 5,569,216,512 |
| PreImageAnchor | 9.49 | 5,596,381,184 |
| PreImageAnchorSelected | 13.29 | 5,706,235,904 |
| SelectedReceivedOracle | 30.34 | 5,646,909,440 |
| RepresentedImageGame | 13.15 | 5,624,152,064 |
| ReferenceIndependentRelation | 10.93 | 5,607,014,400 |
| PreAnchorJoint | 16.67 | 5,780,701,184 |
| PositivePackBinding | 17.17 | 5,562,793,984 |

Use the commands in the focused runners with **new log paths**, not unchanged
heavy replays. Dependencies are reused from their audited cache. The final
small dependency-consuming target is `PreAnchorJoint.lean`; no package-wide
replay or SBF build was started. The independent evidence audit is:

```
python3 docs/research/v8-no-work-100-20260907/experiments/audit_pre_anchor_joint.py --check-recorded
```

The actual successful leaf commands, from the experiments directory, were:

```
bash run_pre_image_anchor.sh pre-image-anchor-v2.log PreImageAnchor
bash run_pre_image_anchor.sh pre-image-anchor-selected-v1.log PreImageAnchorSelected
bash run_pre_anchor_joint.sh SelectedReceivedOracle selected-received-oracle-v4.log
bash run_represented_image_game.sh represented-image-game-v2.log
bash run_reference_independent_relation.sh reference-independent-relation-v2.log
bash run_pre_anchor_joint.sh PreAnchorEligibility pre-anchor-eligibility-v1.log
bash run_pre_anchor_joint.sh PreAnchorJoint pre-anchor-joint-v6.log
bash run_positive_pack_binding.sh positive-pack-binding-v2.log
bash run_pre_image_control.sh pre-image-control-v1.log
```

Those paths already exist and the runners deliberately refuse to overwrite
them. For an authorized changed-dependency reproduction, use distinct paths.

`run_pre_anchor_joint.sh` records research pin bbca32e0 and borrowed formal
source pin `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, hashes the source/olean
import closure and verifies it is unchanged during the check. Its first two
preflights refused the cache because an imported V7 operational-resource
source differs from the research checkout; the replacement explicitly pins
the actual borrowed main source used by the established selected encoder
cache. It does not relabel that source as the research version. Main's
concurrent untracked K13 work is not imported or modified.

Failed leaf logs record only local elaboration/name/inference problems; no
memory cap was increased. Small explicit algebraic/filter interfaces replace
eager reduction. Each retained claim requires exit0 and an axiom audit limited
to `propext`, `Classical.choice`, `Quot.sound`. The JSON records exact hashes,
exit, time, RSS and swap for every successful leaf.
In particular, the sparse branch's filter statements were moved into the
small generic `PreAnchorEligibility` leaf before specialization, eliminating
the concrete-instance recursion failure without raising the recursion cap.
The v5 endpoint already passed; v6 is a changed-statement dependent check
adding the explicit dense-prefix inequality, not an unchanged replay.

The exact maximum census remains
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes. No proof scalar,
nonce, round, padding, parser instruction or verifier operation is added.
The inherited CU results are unchanged and do not certify the opt-in
positive-transfer profile; no new full-transaction SBF result is claimed.

The primary QM31 q22 direction remains worth pursuing: this closes a real
adaptivity/reference-selection link without more proof data or weaker checks.
It does not change the proof body, prove full-view ZK or complete global
knowledge soundness. The single next composition is the **dense correct-image/
correct-row case at B2325 through the existing near-gamma and fixed-early-C1
recovery**, with actual reconstruction/point maps and a checked witness
endpoint. The farther-final accepted-failed-extraction event must remain
visible throughout that work; no bare no-anchor probability target is revived.
