# Prover commitment continuation 38

**Target not yet established.** Intended scope: D146 deployed statement image;
D143 public statement/proof bytes and adversary oracle answers; timing and
other side channels excluded. Intended headline trust list: P1 (shared
SHA-256 ROM), P7, TrustedStd, E1 (successful OS RNG draws), E2 (atomic
create-if-absent and persistence). No trust item is discharged or added here.

Task base: `23392f8056c0fd9d2376d147d7f5ecb97f033aba`.
Branch: `codex/cx-prover-commit38-20261022`. No shipped source changed.

## Stage 1: explicit reservation event and conditional counting

`ProverCommitReservationGuess38.reservationGuess` is the disjunction of an
adversary query matching the generated reservation input and a ledger entry
matching the reservation digest/path. `query_point` and `query_list` bound
query matches for a uniform nonzero nonce. `path_list` bounds ledger matches
for a fresh uniform digest. `fresh_slice` combines these as
`(Q + entries)/(2^256 - 1)` on the explicit product carrier.
`attempt_union` gives `(Q + entries)*attempts/(2^256 - 1)` from per-attempt
bounds without assuming independence among attempts.

These are fixed-context counting theorems, not an E1/native selected-nonce
or adaptive shared-ROM refinement. In particular, the uniform digest in
`fresh_slice` is a P1 fresh-coordinate calculation; it is not substituted for
a memoized answer. The necessary native sampler/history instantiation remains
open. No claim that an imported coupling hypothesis has been discharged.

J9152–J9155 are rejected elaboration drafts (finite/decision instance and
cast normalization); no resource failure or limit increase. J9156 compiles
all seven final top theorems: exit 0, wall 2.00 s, peak RSS 4,061,632 KiB,
zero swaps, axioms only [propext, Classical.choice, Quot.sound]. Every
attempt uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and
Lean -M7000. Source snapshots, source SHA-256, dependency fingerprints,
commands and full raw receipts are in
`evidence/prover-commit38-20261022/lean/attempts.json` and `lean/receipts/`.
Only new job modules are installed; changes to them are snapshotted before
replacement. No inherited shared source/object was overwritten.
