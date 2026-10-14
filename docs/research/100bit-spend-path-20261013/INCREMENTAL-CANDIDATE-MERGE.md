# Reuse the exact joint list through an incremental merge

The new finite merge specification returns exactly the existing width-29
joint candidate list, given complete per-lane lists and a lane schedule
covering all 29 lanes. Every intermediate retained family has at most 100
members. With at most 100 decoded candidates per lane, a 29-lane schedule
visits at most 290,000 candidate pairs in total.

This closes the finite merge's completeness and cardinality argument. It
does not implement or bound the runtime of a per-lane Reed–Solomon decoder,
field arithmetic, agreement testing, or the complete witness extractor.

## The exact specification and invariant

`IncrementalJointCandidates.advance` takes a current lane set `S`, a finite
family supported on `S`, and a supplied next-lane list. It forms pairs,
updates the next coordinate, and retains tuples agreeing with the received
word on at least 38,230 common positions across all selected lanes.

`advance_supported` preserves zero coordinates outside the enlarged lane
set. `advance_card_le_100` applies the existing
`PartialJointList.partial_family_card_le_100`; its threshold premise is
derived from the filter, not supplied by the caller.

For any tuple in the old full `Lambda`, the old projection theorem supplies
the same agreement threshold after selecting any subset of lanes.
`advance_preserves_full_projection` uses this fact and the coordinate-update
identity to show that a valid full tuple's projection survives the next
merge, whenever its next coordinate is in the supplied lane list.

`IncrementalCandidateLoop.run` repeats that step, starting from the singleton
zero tuple with no selected lanes. `run_preserves_projection` proves the
invariant by induction. `full_candidate_coordinate_close` derives each
needed coordinate's membership in the old scalar `Close` set from joint
agreement-set containment.

`candidates_eq_lambda` consequently has two substantive input premises:

- the lane list covers all 29 coordinates;
- each supplied decoded set contains the old `Close` set for that lane.

It concludes equality with the old `InitialResponses.Lambda W`. Extra
per-lane candidates do not require a separate soundness assumption: the
final joint-agreement filter enforces the exact full-list specification.
The 100-member retained-family bound holds independently of a bound on the
supplied decoded sets.

For the pair count, `IncrementalCandidateCost.pairs` records the product of
the two list cardinalities at each step, then recurses on the filtered
family. `pairs_le` additionally assumes that each supplied decoded list has
at most 100 members. It proves at most `10000 * lanes.length` pairs;
`initial_pairs_le_290000` specializes to length 29. This count does not
include the cost of evaluating a candidate or testing agreement at the
1,048,576 domain positions.

## Direct reuse of the old semantic padding

`C1SemanticPadding.projectWord_eq_c2Words` identifies the new C1 projection
onto lanes 0–25 and 28 with the old semantic context's zero padding of lanes
26 and 27. `candidates_eq_old_Lambda` then gives literal equality of those
candidate sets. It reuses `exactInitialEncoder_zero` to justify the old
padding word; no new semantic premise is introduced.

This identity does not establish that the actual committed bytes decode to
that typed semantic context. It also does not instantiate the causal
Fiat–Shamir classifier or its local probability bounds.

## Evidence and remaining work

Base revision: `209663b6e8bd07a5067eb5dce3cf11e02e438a0d`.
Four component modules and `CandidateReuseCheckpoint` were compiled on the
NUC under 4G/6G/zero-swap limits. The checkpoint exited 0 in 1.38 seconds,
with 3,537,744 KiB peak RSS and zero swap. Its 20 axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. Exact sources, attempts,
objects, and receipts are in `evidence/lean-candidate-reuse-20261014/`.

The [dated reuse inventory](INCREMENTAL-CANDIDATE-REUSE-INVENTORY.md) records
the prior APIs and the transition from the missing loop to these checked
results. The [GRS route](GS-DECODER-REUSE-PATH.md) describes the remaining
per-lane decoder and image-inversion work. The finite specifications still
use classical finite-set operations. No executable decoder refinement,
full extractor complexity theorem, source correspondence, or zero-knowledge
theorem is claimed by this checkpoint.
