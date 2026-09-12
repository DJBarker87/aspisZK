# Live q22 schedule to authenticated increment — 2026-09-12

`lean/SameBodyLivePreparedIncrement.lean` removes the independently supplied
typed-query seam from the authenticated increment constructor.  Success of
the actual `middleQueryRhoScript` is peeled to success of its literal
`queryRhoScript` suffix from the exact reached transcript.  The existing
suffix trace then proves that the returned list is duplicate-free, contains
exactly 22 values below 262,144, and precedes the same nonzero rho.

`liveScheduleFromRun` constructs `Fin 22 -> Fin 262144` directly from that
returned list and its derived facts.  `prepareFromRun` passes precisely this
schedule, the same alpha0 and the same rho into the already checked
same-body opening/Merkle pipeline.  `prepareFromRun_success` proves those
three inputs are retained by `Prepared`; no schedule-equality premise occurs.

This is deterministic content and causality only.  It does not prove query
uniformity, freshness, authentication-prefix/log construction, successful
opening preparation, terminal relation acceptance, payment extraction or
literal Rust refinement.

## Focused evidence

- Base revision: `d1a195ec9d29d8ebbf3502880e59b65edcedf45d`
- Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Capped NUC compile: `MemoryHigh=8G`, `MemoryMax=9G`,
  `MemorySwapMax=0`, `-j1 -M8192`
- Exit: 0
- Wall time: 3.47 seconds
- Peak RSS: 6,741,868 KiB
- Swap: 0
- Source SHA-256:
  `e0c46dcfec8d97e284e35f03449f2b8f3b64ebe4bdddb2c548e9f7a2ceef809d`
- Olean SHA-256:
  `6826c4ad33cb23d40bce18186eacd2fdbeb0088559b365595e76a69d20a92fb0`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

