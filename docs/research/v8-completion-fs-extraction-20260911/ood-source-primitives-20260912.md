# OOD source primitives — 2026-09-12

`lean/SameBodyOODSourcePrimitives.lean` closes two deterministic prerequisites
identified in the review of `SameBodyOODData`.

First, any point returned by the concrete V7 secure-circle decoder has two
coordinates that canonically decode back to exact QM31 values.  The result is
proved both for one decoder call and for the successful branch of the actual
bounded first-point and distinct-second-point retry traces.  Rejected retries
remain explicit in the inductive traces.

Second, the source OOD-answer builder and ordinary-relation projection use the
same field-number formula, `359 + 29*sample + lane`.  Their projected values
are definitionally equal for the same parsed list.  This is mathematical
layout alignment, not yet literal Rust parser refinement.

The next composition still has to extract the successful first/distinct trace
witnesses from one globally successful `sourceGammaTrace`, run
`SameBodyOODData.fromSampled`, and retain its possible selected-coordinate
inverse failure.  No freshness, distribution, terminal acceptance, or
probability statement is made here.

## Focused evidence

- Base revision: `5c5284ef7646142c8a597c6c712e27feb9e8555c`
- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Command: focused `lean -j1 -M8192 -o
  /tmp/SameBodyOODSourcePrimitives.olean` under `MemoryHigh=8G`,
  `MemoryMax=9G`, `MemorySwapMax=0`, `RuntimeMaxSec=600`
- Exit: 0
- Wall time: 2.83 seconds
- Peak RSS: 6,612,604 KiB
- Swap: 0
- Source SHA-256:
  `c98dedc9dfb1271f8adc59bc99ed30837616a68f273dd7ba184bf0f80d147d63`
- Olean SHA-256:
  `f6249b916fd88b0d95dfc23671fb8629dc6a6358833475353dc7ea65a3cabc6d`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
