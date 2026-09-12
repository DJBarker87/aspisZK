# Gamma target restoration adapter — 2026-09-12

`lean/FSV8GammaTargetRestorationAdapter.lean` connects the computed V8 gamma
input's three-way target disposition to the existing V7 K1.6 restoration
boundary.

When the input is represented in the adversary's frozen `q1`, the adapter
constructs the exact fixed replay record through `gammaBoundaryConfiguration`
and runs `ExtractionCollectorSource.sourceAttempt`.  A checked attempt yields
both successful `constructLegalReplay` and checker acceptance.  The table-hit
and absent-table cases remain distinct outcomes; neither is silently called a
fresh successful programming opportunity.

This is a deterministic adapter.  It does not prove that the adversary made
the query, that an absent target can be programmed within resources, that a
fork succeeds, that the selected verifier accepts, or that the actual random
oracle execution has the required distribution.  Those are still the
substantive Fiat–Shamir obligations.

## Focused evidence

- Base revision: `fab0340774767d15f26458b84a496b1533b53a11`
- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Command: focused `lean -j1 -M8192 -o
  /tmp/FSV8GammaTargetRestorationAdapter.olean` under `MemoryHigh=8G`,
  `MemoryMax=9G`, `MemorySwapMax=0`, `RuntimeMaxSec=600`
- Exit: 0
- Wall time: 2.66 seconds
- Peak RSS: 6,615,960 KiB
- Swap: 0
- Source SHA-256:
  `1fd6c1d06c66ccb85aa33db55a54257d1471726ffb4ea5bbae8e96ede45138ca`
- Olean SHA-256:
  `2819677c6b947cbe8b7a2b900640b200368a8e1ce1f6a27d97671ea43e112648`
- Axioms: none for record placement; `propext`, `Classical.choice`,
  `Quot.sound` for checked replay.
