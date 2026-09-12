# V7-produced prehistory to current V8 continuation

Status: **deterministic ideal finite-tape continuation constructed; actual
adaptive-source/ROM coupling open**.

`lean/FSV8V7PrehistoryContinuation.lean` composes the fresh-history projection
with the whole-script interpreter refinement.  A V7 lazy-oracle prehistory is
run from `emptyOracle` on one finite fresh-answer tape.  Its actual resulting
oracle state is projected into the current interpreter, and an arbitrary
bounded current V8 `Script` is then run from that produced state on the same
tape.  The theorem derives exact visible halt correspondence and exact final
projected-state equality; it does not take `StateAligned`, a cache, a history,
or a projected-prefix equality as a premise.

The remaining hypotheses are the literal total-call, fresh-call, and tape-room
bounds on the state produced by the prehistory.  They are resource bounds, not
acceptance or extraction assumptions.

This result does **not** construct an actual adversarial/source prehistory and
does not couple a deployed random oracle to a finite independent tape.  The
separate [premise map](v7-v8-source-coupling-premise-map-20260912.md) records
why the inspected V7 fixed-run, restoration and K1.6 leaves do not already
supply that generic producer.

## Focused evidence

- Base revision: `64ebf012`.
- Target: `FSV8V7PrehistoryContinuation.lean`.
- Source SHA-256:
  `70cf1e72612432292b214d0bc799d1ca5fb3582f9efce23f876599fb41705359`.
- Artifact SHA-256:
  `c84879d6eb4b0c1907edc7b58e7f9d887f5b586f03be83a7a5a9502808cd0e3f`.
- NUC/Tailscale compile: exit 0, wall 2.71 seconds, peak RSS
  6,527,128 KiB, zero swap, `MemoryHigh=8G`, `MemoryMax=9G`,
  `MemorySwapMax=0`.
- Both promoted declarations report only `propext`, `Classical.choice`, and
  `Quot.sound`.

No broad replay, probability calculation, protocol change, or proof-byte
change was made.
