# Source relation producer — ordinary scalar milestone

`lean/SameBodySourceRelationProducer.lean` removes the arbitrary ordinary
scalar from the previous terminal interface.

`ordinaryOps` instantiates the source-shaped ordinary arithmetic with exact
QM31 operations and the existing fail-closed `qm31TryInv`. `corrected` then
executes the repaired `[kappa,kappa^2,kappa^3]` row batching, the two OOD-row
batches, selected-coordinate chord interpolation, and the public affine
correction on `Ready.input.word`.

`buildOrdinary` preserves `none` as explicit inverse/domain rejection. Its
successful `OrdinaryReady` branch contains both the same-body OOD-data
provenance (`fromSampled ... = some ready.data`) and the actual successful
correction result. `ordinary_claim_constructed` proves the resulting claim is
the literal repaired row/OOD/public correction expression.

`complete` constructs the prior `SourceRelationProducer` with that derived
claim. It also fixes `early` to the literal first 417 fields of the canonical
word. The only remaining producer fields are grouped in `CausalRemainder`:

- a pre-tau causal relation strategy;
- its realised canonical-word equality; and
- the final 256-entry ordinary/image terminal weight.

The OOD-data provenance equality is still an interface until the chronological
`SameBodyOODData.fromSampled` constructor is spliced into the parent run.
Neither a favourable inverse, causal equality nor terminal weight is assumed
by `buildOrdinary` itself.

## Focused evidence

- Base revision: `66400a885c8426897200d74aa396b15385717086`
- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, `-j1 -M8192`
- Exit: 0
- Wall time: 2.85 seconds
- Peak RSS: 6,757,036 KiB
- Swap: 0
- Source SHA-256:
  `2c3edaa51b73e348759629cded5c68fc0709171f0d0b1dbd84bf3a623bea806b`
- Olean SHA-256:
  `4dfdd1f847a5d1bd3378b49fd893b6815c55094fdc2bc236748fa9f4e929a006`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
