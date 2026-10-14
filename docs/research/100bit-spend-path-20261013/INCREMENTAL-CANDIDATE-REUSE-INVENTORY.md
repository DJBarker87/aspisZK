# Incremental candidate completeness reuse inventory

This inventory was assembled before implementation of the lane-by-lane loop, from the prior read-only snapshot at `HEAD=e21211727fc6ad53a2ef014d3fa3dda72037cef0`. It records reusable finite-set APIs and the proof route they support; it does not establish an efficient decoder or a protocol-level source correspondence.

## Existing declarations and exact roles

- `AspisR1.PartialJointList.projectWord` and `projectMessage` (`lean/PartialJointList.lean:18-24`) replace every lane outside a selected `Finset (Fin 29)` by zero.
- `selectedSupport` (`PartialJointList.lean:26-29`) is the set of `Fin 1048576` indices `x` for which all selected lanes agree: `∀ lane, lane ∈ S → W lane x = exactInitialEncoder (t lane) x`.
- `selectedSupport_eq_joint` (`PartialJointList.lean:35-50`) identifies this set with `width29JointAgreementSet exactInitialEncoder (projectWord S W) (projectMessage S t)`. That joint agreement set is `univ.filter` over the coordinate agreement predicate in `AspisFormal/AspisFormal/V6Width29CorrelatedAgreement.lean:102-108`.
- `projected_response_mem_lambda` (`PartialJointList.lean:52-69`) states that `t ∈ InitialResponses.Lambda W` implies `projectMessage S t ∈ Lambda (projectWord S W)`. Its proof gives containment of the original joint agreement set in the projected one, preserving the 38230 support threshold.
- `partial_family_card_le_100` (`PartialJointList.lean:75-105`) bounds a finite family by 100 when every member is zero outside `S` and has selected support at least 38230. It zero-pads the family and applies `jointInitialList_card_le_100` (`Wide/JointList.lean:27-32`).
- `InitialResponses.Lambda` and `Close` (`lean/InitialResponses.lean:25-31`) are filtered finite sets; `mem_Lambda` and `mem_Close` give their threshold characterizations (`:40-43`). `Lambda_card` and `Close_card` bound them by 100 (`:45-61`).
- The coordinate fact needed to use per-lane lists is direct: for `t ∈ Lambda W`, the full joint agreement set is a subset of the single-coordinate agreement set for each `lane`, by specializing the joint predicate at that lane. `full_candidate_coordinate_close` packages this implication as `t lane ∈ Close (W lane)`.

## Reusable one-step update facts

`IncrementalJointCandidates.advance` (`lean/IncrementalJointCandidates.lean:16-22`) takes a product of a prior tuple family and a decoded coordinate set, maps each pair through `Function.update`, then filters by the selected-support threshold for `insert lane S`.

The green component module supplies these reusable facts:

- `advance_supported` (`:24-40`) preserves zero values outside the selected lanes after an update.
- `advance_card_le_100` (`:42-52`) applies `partial_family_card_le_100`; the threshold premise is derived directly from membership in `advance`'s filter.
- `unfiltered_image_card_le` and `unfiltered_image_card_le_10000` (`:54-74`) bound the product/image before filtering, including the direct `100 × 100` consequence when both inputs have at most 100 members.
- `projectMessage_insert` (`:76-84`) identifies the next projected tuple with `Function.update (projectMessage S t) lane (t lane)`.
- `selectedSupport_project` (`:86-95`) states that projecting a tuple on `S` leaves its selected support unchanged.
- `projected_full_threshold` (`:97-106`) transfers a full `Lambda` tuple’s threshold to any selected projection, using `projected_response_mem_lambda` and `selectedSupport_eq_joint`.
- `advance_preserves_full_projection` (`:108-120`) states the one-step completeness membership: if the current projected tuple is in the prior family and `t lane` is in the decoded lane set, then the new projection is in `advance`.

The membership proof uses the pair `(projectMessage S t, t lane)`, then the product/image membership constructors, `projectMessage_insert`, and the projected threshold. It does not enumerate the tuple space.

## Iterated loop and completeness invariant

The root-owned `lean/IncrementalCandidateLoop.lean` now defines `run` recursively over a supplied lane list. At each step it invokes `advance`, adds the lane to `S`, and passes that lane’s supplied decoded set. Its public lemmas state:

- `run_supported`: all outputs are zero outside the union of the starting selected lanes and the processed lane set.
- `run_card_le_100`: the finite family remains bounded by 100 throughout the loop.
- `run_preserves_projection`: for a fixed full tuple `t ∈ Lambda W`, if its projection belongs to the initial family and every processed coordinate is present in its supplied decoded set, its final projection remains in the loop output.
- `run_close`: every loop output retains the 38230 selected-support threshold.
- `full_candidate_coordinate_close`: each coordinate of a full `Lambda` tuple is in that lane’s `Close` set.
- `candidates_card`: the loop seeded with the singleton zero tuple has at most 100 outputs.
- `candidates_eq_lambda`: if the lane list covers `Fin 29` and each supplied decoded set contains the corresponding `Close` set, the result equals `Lambda W`.

The intended completeness proof is the direct induction through `run_preserves_projection`; `full_candidate_coordinate_close` supplies its per-coordinate premise. `run_close` supplies the converse inclusion through the final support threshold once the lane list covers all 29 lanes. This is a finite-list set-theoretic result. It does not implement or bound the cost of producing each per-lane decoded set.

## Reduction and scope review

The current loop source uses structural induction over the explicit lane list. Its empty-support and full-support equalities are proved extensionally over an arbitrary index with `Finset.ext`; no `Finset.univ` enumeration, recurrence unfolding, large numeral evaluation, or exhaustive `decide` is present in the inspected source. The largest coordinate type is visible in predicates, but the proofs reason pointwise and do not enumerate its 1,048,576 elements.

The file’s lane-local close proof uses the `agreementSet` identifier; the current source explicitly qualifies it as `AspisV5FriCoherentCandidateExtraction.agreementSet`. The exact namespace must continue to match the imported source API. At the time of this inventory’s initial inspection, the loop file was root-owned and had not yet been compiled, so its elaboration and axiom audit were then pending. The **Current update (2026-10-14)** below supersedes that historical status and records the green focused result.

## Current update (2026-10-14)

The inventory above predates implementation of the loop module. The independently owned `IncrementalJointCandidates.lean` now includes the projection/one-step membership lemmas listed above and has a focused green result at attempt `incremental-joint-candidates-g` (source SHA-256 `4a4d6aaa6cc6bc7d787d2b14315876dfaf683b46227b1fdaada2f12f629b7142`; exit 0; 1.63 seconds; peak RSS 3,145,500 KiB; swap 0). Its eight axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The loop source is now present at `lean/IncrementalCandidateLoop.lean` and passed root’s focused compile: attempt `incremental-candidate-loop-c`, source SHA-256 `3304883df4d6802726fa65ba5a5a27a12e3cd18806db680c6b5cf6c3a61c9524`, exit 0, 1.92 seconds, peak RSS 3,150,820 KiB, zero swap, with seven axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`.

The exact assumptions of `candidates_eq_lambda` are explicit: `lanes.toFinset = Finset.univ` and `∀ lane, Close (W lane) ⊆ decoded lane`. It proves equality of the finite candidate family with `Lambda W`; it does not provide a procedure or runtime bound for constructing those decoded sets. The separate `IncrementalCandidateCost.lean` module counts only the candidate pairs presented to each update. Its focused target `R1IncrementalCandidateCost` passed attempt `incremental-candidate-cost-a`, source SHA-256 `d8b1b8069de79af73977b67fca7e2234ad7008b4cf3be514a286a24300dde393`, exit 0, 1.42 seconds, peak RSS 3,152,444 KiB, zero swap; all three axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The 290000 result assumes exactly 29 lanes and each supplied decoded set has cardinality at most 100. This is a pair-count bound only, not a bound on per-lane decoding or total runtime.

The current worktree revision during these updates is `209663b6e8bd07a5067eb5dce3cf11e02e438a0d`.

## Source pins

Current source hashes at this update:

- `lean/PartialJointList.lean`: `8ecf2399077ca31a3888bd5cefdc75fdc8cef8fc6dbc310b13f23182d4da68af`
- `lean/InitialResponses.lean`: `5a67cc4cb4db77f04e9f8f0d53c2d8ac1650f4fc01b130073c790bee89f3fd8d`
- `lean/IncrementalJointCandidates.lean`: `4a4d6aaa6cc6bc7d787d2b14315876dfaf683b46227b1fdaada2f12f629b7142`
- `lean/IncrementalCandidateLoop.lean`: `3304883df4d6802726fa65ba5a5a27a12e3cd18806db680c6b5cf6c3a61c9524`
- `lean/IncrementalCandidateCost.lean`: `d8b1b8069de79af73977b67fca7e2234ad7008b4cf3be514a286a24300dde393`
