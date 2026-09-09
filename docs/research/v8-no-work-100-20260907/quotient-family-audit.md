# Literal quotient family: finite bound and relation composition

Read-only audit at research HEAD
`b006d34ffc6d552cd5ecd9f292cf2bd095f7fdb9`. No Lean/Rust build or unchanged
replay was run. The audit derives a concrete cardinality bound from existing
encoder and Johnson facts and identifies the still-unpackaged bridge. It does
not claim a newly kernel-checked selected-family theorem.

## The family and its fixing boundary

For one arbitrary fixed received quotient word
`R : Fin 1048576 -> QM31Exact`, define

```
S_R(Q) = {i : Fin 262144 |
  for every slot : Fin 4,
    exactInitialEncoder Q (childIndex i slot) = R (childIndex i slot)}

F_a(R) = {Q : Fin 1024 -> QM31Exact | a <= |S_R(Q)|},  a = 9558.
```

The subscript a is the agreement threshold, **not the sampled fold challenge**.
The family contains all natural1024 quotient candidates above that floor,
with no image test, decoder filter, provider success, or component-tuple
membership premise. It is finite because the field and coefficient dimension
are finite. Its actual cardinality depends on R; the bounds below are not a
claim that it has exactly 99 members.

For the V8 application, R may depend on both sequential component OOD vectors,
the chord, gamma, and earlier messages. The family is nevertheless fixed
before kappa, tau, response0, alpha0 and final256, provided R is fixed at that
boundary. This is the useful causality for a row/image union bound. It is not
a pre-gamma family and cannot justify early C1 or gamma component root counts.

This four-lane quotient family is **not** the older family of 29 original-code
component tuples. The old cardinality cap100 is useful proof architecture,
not an identification of the two families.

## Why the whole-fibre overlap cap is 255

Define the four coefficient lanes of Q by
`q_lane = coefficientLane 256 lane Q`. Define the four received lane values
at fibre i by the actual local decoder

```
radix4Decode inverse2y(i) (-inverse2y(i)) inverse2x(i)
  (fun slot => R(childIndex i slot)).
```

The existing exact encoder/lift theorem and the two-sided local inverse show
that whole-fibre equality is equivalent to **all four** decoded received lane
values equalling `exactFinalLinear q_lane i`. This is a local identity for
arbitrary received values, not an assumption of global polynomiality.

If Q and Q' differ, at least one coefficient lane differs. On a common whole
fibre their differing lanes' final codewords agree. The selected final encoder
has overlap at most **255**, so

```
|S_R(Q) intersection S_R(Q')| <= 255.
```

There is no four-lane union factor: choose one differing lane. The maps
`Q -> (coefficientLane 256 lane Q)_lane` and
`u -> (fun index => u(slotIndex index)(parentIndex index))` are inverse by the
existing child/parent/slot identities. Thus counting coefficient tuples and
counting literal Q values are the same finite problem.

The 255 bound is stronger than dividing the older 1,024-symbol circle root
cap by four to obtain 256. That older cap is correct but loses the exact
four-lane structure relevant here.

### Existing exact APIs

| Mathematical step | Existing source/API | Status for this audit |
| --- | --- | --- |
| Stored log20 encoder is the lift of the stored log18 line encoder | `K1/V7Tag73ExactOneFoldEncoderBinding.lean`, `exactInitialEncoder_eq_circleLift` | Existing checked selected mathematical encoder theorem |
| Literal child fibre evaluation | `V5FriConcreteEncoderCommutation.lean`, `radix4LiftEncoder_apply_child`, `circleLiftEncoder` | Existing checked generic identity |
| Both directions of local four-slot inversion | Same file, `radix4Decode_radix4Evaluate`, `radix4Evaluate_radix4Decode` | Existing checked identities; actual nonzero inverse premises are required |
| Selected inverse identities | `K1/V7Tag73CanonicalOneFoldSchedule.lean`, `canonical_one_fold_schedule_exact` | Existing selected schedule fact |
| Lane/interleave inverse | `coefficientLane_apply`, `parentIndex_childIndex`, `slotIndex_childIndex`, `childIndex_parentIndex_slotIndex` | Existing checked identities |
| Exact final overlap cap | `V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder_overlap_cap` | Existing checked cap255 with distinct stored points and natural degree255 |
| Whole-fibre family intersection cap255 | The composition just described | **Derived here, not yet a named checked selected-family leaf** |

`ExactFoldSelected.fullQuotient_iff_lift` already reuses this same selected
encoder/lift equality. `FoldSupportClosure` supplies related four-fold/full-slot
transport, but no fresh fold samples are necessary to prove this static family
intersection cap. The old `NearGammaFibreBridge.full_fibre_overlap_le_256` does
not by itself establish the sharper cap.

## Existing Johnson theorem gives at most 99

The reusable API is
`AspisV5FriJohnsonListBound.list_card_lt_of_johnson_parameters`. For a finite
subfamily, take its subtype as `Candidate`, the whole-fibre support as
`agreement`, and use parameters

```
wordSize=262144, agreementFloor=9558, overlapCap=255,
boundPlusOne=100.
```

The exact checks are

```
9558^2 - 262144*255 = 24,508,644 > 0,
262144*(9558-255) = 2,438,725,632,
100*24,508,644 - 2,438,725,632 = 12,138,768 > 0,
262144/2 = 131,072 <= 100*9558 = 955,800.
```

Together with `255 <= 9558`, these discharge the theorem's arithmetic
hypotheses and imply `card < 100`, hence **card <= 99**. The displayed Johnson
fraction is exactly `2438725632/24508644`, approximately 99.50471483. Using the
weaker cap256 instead gives approximately 100.56971060 and only cap100.

`RelaxedTupleFamily.relaxed_joint_family_card_le_100` gives the reusable proof
pattern: subtype a finite family, derive intersections from a differing lane,
then call the generic Johnson lemma. Its separate
`finite_predicate_cover` theorem constructs a mathematical full family from a
uniform finite-subfamily bound. The concrete width29 statement cannot simply
be invoked on the present four-lane quotient type.

Thus cap99 is a fully specified mathematical consequence of existing checked
ingredients, pending the small literal support/interleave composition and
selected Johnson instantiation. This audit did not compile that endpoint.
Finite enumeration of the enormous coefficient universe is not proposed as a
resource-bounded extractor.

### Optional integer refinement: at most 92

A discrete second-moment calculation sharpens the mathematical bound further,
but is **not needed** for the proposed cap99 composition and is not a newly
checked family theorem.

If 93 candidates existed, select those 93 and let m_i be their integer
incidence count at coordinate i. Then

```
sum_i m_i >= 93*9558 = 888,894.
```

For every nonnegative integer m,
`choose(m,2) >= 3*m-6`, equivalently `(m-3)*(m-4) >= 0`. Therefore

```
sum_i choose(m_i,2) >= 3*888894 - 6*262144 = 1,093,818.
```

But the 93 choose 2 distinct candidate pairs each overlap on at most255
coordinates, giving

```
sum_i choose(m_i,2) <= 255*choose(93,2) = 1,090,890.
```

The gap is **2,928**, a contradiction, so cap92 follows. For92 candidates this
same tangent gives lower1,065,144 versus upper1,067,430, so it does not exclude
92. This does not prove that a list of size92 is attainable or optimal. It is
an optional finite-integer sharpening, not an invitation to spend the current
run proving a smaller constant whose practical effect is minor.

## Conditional composition for represented bad candidates

Freeze the actual R, chord, four ordinary covectors and claims before kappa,
and construct the family there. For Q in the family define its image residual
and the four shifted ordinary row errors through `replaceRows rows Q`.
Those errors are fixed before kappa; the first response may depend on kappa
and tau, and the actual final may depend on alpha.

The relevant supported event is

```
actual final256 = coefficientFoldLayer 256 alpha Q
AND (Q has an invalid image OR its shifted row error vector is nonzero).
```

This is about the prover's **actual** selected final, not merely existence of
some unrelated family member. The bad-candidate property is fixed before
kappa; representation is determined only after the actual final is known.

The existing `RepresentedImageGame` statements already handle arbitrary
received words on this event. In particular:

- `represented_bad_anchor_bound` charges two tau roots for an invalid image,
  the first degree-six relation repair and the shared suffix.
- `represented_wrong_rows_bound` charges three kappa roots for image-valid
  wrong rows, without an extra tau charge.
- `represented_image_or_rows_bound` partitions those two fixed cases and
  uses their uniform ceiling; it does not add both root losses.
- `ReferenceIndependentRelation.supported_rows_probability` and
  `rows_accepts_iff` prove that replacing the analysis reference changes no
  executed claim, weight, response, received slot or acceptance outcome.
  The supported predicate itself must be held fixed during that transport.

An outer finite-family union is legitimate because the whole family precedes
kappa/tau, even though the represented member can be selected adaptively. It
must not move this family backwards through gamma or the component OOD rounds.

### Charge shared suffix events once

Blindly multiplying the full per-candidate theorem by99 is a valid coarse
union but unnecessarily repeats query batching and later repairs. A more
precise event partition is:

| Event | Fixing boundary and fresh challenge | Family factor |
| --- | --- | --- |
| Invalid-image mixture cancellation | Fixed Q and kappa before fresh tau; degree2 | At most `2*L_image/(k-1)` |
| Image-valid wrong-row cancellation | Fixed Q and four errors before fresh kappa; degree3 | At most `3*L_row/(k-1)` |
| First relation repair outside those cancellations | Fixed Q, kappa, tau and response0 before fresh alpha; degree6 | At most `6*(L_image+L_row)/k` |
| Shifted query-batch cancellation after a remaining nonzero actual prior | Actual prefix and queries fixed before fresh rho | `q/(k-1)`, **once**, not once per Q |
| Three later relation repairs | Sequential actual compact responses/challenges | `18/k`, **once** |

Here `L_image+L_row <= L <= 99`, and image-invalid candidates are not counted
again as row-invalid candidates. Outside the first three exceptional unions,
any represented bad Q forces the actual post-alpha prior nonzero.
`FirstImageDiscrepancy.firstError_eval` and reference independence give that
literal equality; no target is frozen before its real fixing boundary.
`RelationCompatibleMoment.schedule_false_bound` then handles the one actual
shifted batch and tail, including adaptive ordered-query handling.

With q22, the resulting proposed family/suffix ceiling is

```
(3*99+22)/(k-1) + (6*99+18)/k
= 319/(k-1) + 612/k,
k=(2^31-1)^4.
```

The outer family/event partition is mathematically justified as above but is
not yet a kernel-checked family wrapper in this audit. The existing checked
per-candidate theorem gives the coarser direct union if needed. Do not present
the sharper composed formula as an already completed source theorem.

Most importantly, **no factor99 belongs on the unrepresented-final query
moment**. That event concerns the one actual final and the fixed received
word, and the new alpha-tail calculation treats it directly. A clean global
organization is: one unrepresented-final contribution, one represented
bad-family mixture/first-repair contribution, and one common rho/later-repair
budget. The shared suffix terms already present in any previously quoted
subtotal must not be added a second time. The old396430 inventory is not
imported by this audit.

## Remaining limitations and next bridge

An image-valid, correctly row-bound quotient in this family is not yet a
width29 component tuple or a checked payment witness. Gamma component
coverage, earlier C1-before-lambda/chi causality, efficient extraction,
authentication/replay/source coupling, full-view privacy and resource-bounded
Fiat–Shamir remain separate. The arbitrary-word family definition needs no
polynomial representation of R; the selected Rust virtual-word connection
still needs the actual source interface, including pole handling.

The smallest formal next step is the whole-fibre/decoded-four-lane agreement
equivalence and its255 intersection cap, followed by the existing generic
Johnson API at the four exact parameters above. Then an outer finite-family
root-event wrapper can consume the already checked represented relation
theorems while leaving the unrepresented query term and good-row component
recovery untouched. No new field, query, proof byte, or verifier operation is
required for this proof-layer composition, and no global security conclusion
is claimed here.
