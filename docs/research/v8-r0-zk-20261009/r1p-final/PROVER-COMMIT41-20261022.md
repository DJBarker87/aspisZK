# Prover commitment continuation 41

**Target not yet established.** Work in progress on D153's public-prefix
conditional ROM law. Trust items and endpoint are unchanged.

## Stage 1: conditional frozen-table law

`ProverCommitConditionalRom41.conditional_law` proves the exact ROM
programming law jointly with an arbitrary observation determined by frozen
coordinates. Its indicator form includes impossible observations without
conditional division. `history_fiber` proves both directions of equality
with an ordered adaptive history when that history's addresses are frozen;
`programmed_history` applies this to frozen programming. Repetitions and
termination are preserved, and a retained rejected-attempt prefix is not
removed from the list. These generic results do not yet discharge the
concrete private continuation or replace `EventsR1PBin.hit_cm`.

J9187–J9188 are rejected namespace drafts. J9189 compiles the three final
theorems, exit 0, wall 1.83 s, peak RSS 4,043,272 KiB, zero swaps. All
printed axioms are subsets of [propext, Classical.choice, Quot.sound].
The exact target, source SHA, dependency fingerprint, source revision plus
overlay, commands and raw receipts are retained under
`evidence/prover-commit41-20261022/lean/`. No inherited module was overwritten;
only part-41 drafts were replaced and snapshotted on the host.
