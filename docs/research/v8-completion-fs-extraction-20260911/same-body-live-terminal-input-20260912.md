# Same-body live terminal input — 2026-09-12

`lean/SameBodyLiveTerminalInput.lean` constructs the algebraic terminal input
from one literal transcript body and one successful live later-relation
suffix.  It converts each transcript `UInt8` through the already proved V7
byte bridge, runs the source-shaped sequential canonical parser, and returns
`none` rather than constructing a default word when body length or any field
limb is invalid.

On success, the 697-field relation word, all 24 compact response fields and
all 256 final coefficients are projections of that one decoded body.  The
three terminal coins are exactly the sequential alpha1–alpha3 results from
`FSLiveLaterRelationSuffix.Success`; no caller-supplied later challenge enters
the record.

The query increment remains an explicit `IncrementProducer`.  The theorem
records exactly which bytes that producer supplied to the live transcript but
does not validate the pinned Rust arithmetic behind them.  The leaf does not
construct a causal `SameBodyRelation.Strategy`, ordinary claim or terminal
weight, call `SameBodyRelation.consume`, assume `terminalZero`, or establish
terminal relation/payment acceptance.

## Focused evidence

- Base revision: `89a59114` (the live suffix checkpoint; compilation occurred
  while the shared branch advanced independently)
- Toolchain: Lean 4.32.0, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Command: capped single-file Lean compilation on the NUC with
  `MemoryHigh=8G`, `MemoryMax=9G`, `MemorySwapMax=0`, `-j1 -M8192`
- Exit: 0
- Wall time: 3.65 seconds
- Peak RSS: 6,603,180 KiB
- Swap: 0
- Source SHA-256:
  `47b7989380103f8b7edbf043b59c0354a58e275a39d5831576ed68feef253438`
- Olean SHA-256:
  `1b313a7613b9d429d1d05a6537666507a2ca605d7c4e3d02995b03f5ffb08229`
- Axioms: `propext`, `Classical.choice`, `Quot.sound`

The focused import environment used the pinned V7 Lake path, the recorded
higher-Y overlay and the current completion worktree.  This is a focused leaf
check, not the clean first-party closure replay.
