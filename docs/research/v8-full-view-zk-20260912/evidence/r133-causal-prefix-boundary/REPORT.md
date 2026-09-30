# R133 verified evidence: causal first-hit and typed selected prefix

Date: 2026-09-30 (UTC)

## Verified targets

All nine focused leaves exited 0 with swap 0 under the recorded 5G/7G
`MemorySwapMax=0` runner:

* `CausalFirstHitUnionBound`: 1.59 s, 3239908 KiB.
* `UniformFrameCollision`: 1.69 s, 3237860 KiB.
* `CausalInjectiveFrameBound`: 1.46 s, 3235324 KiB.
* `CausalDuplexCollisionBound`: 1.73 s, 3248480 KiB; includes the symbolic
  `sum_two_prior_slots` and `causal_duplex_two_address_bound` results.
* `SourceFramePrefix`: 1.47 s, 3233072 KiB.
* `RelationPrefixQueryBound`: 1.90 s, 3715728 KiB.
* `CausalTapeFirstHit`: 1.59 s, 3237588 KiB.
* `SelectedResearchPrefixProgram`: 1.87 s, 3719004 KiB.
* `RelationPrefixCorrespondence`: 1.66 s, 3715864 KiB.

The recorded axiom audit is standard (`propext, Classical.choice, Quot.sound`)
for the applicable leaves; `CausalTapeFirstHit`'s `past_update_self` uses the
`propext, Quot.sound` subset, and `RelationPrefixCorrespondence` records the
same subset.

## Boundary

`SelectedResearchPrefixProgram` directly uses the typed circle-pair program
and preserves circle and nonzero `Except` errors.  `RelationPrefixCorrespondence`
still requires its explicit `BridgePremise`; that premise is unproved and is
not silently discharged by compilation.

The structural caps are 1600 pre-q22 and 1815 through rho under explicit
component bounds. Type/source correspondence, actual callback/tape
instantiation, GRIND/source callback equivalence, and source sampler
distribution remain open.
No privacy or soundness claim is made.
