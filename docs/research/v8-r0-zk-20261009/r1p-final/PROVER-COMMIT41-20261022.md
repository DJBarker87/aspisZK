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

## Stage 2: concrete public prefix and mixed read agreement

`ProverCommitPublicPrefix41` instantiates the conditional law at the finite
byte ROM. Its context retains the exact prior adaptive history plus three
ordered public reads: `H(pub)`, the precommit binding, and the attempt binding.
The public nonce policy is an arbitrary function of the fixed prior history.
`reads_of_slice` connects a coherent digest/first-answer slice to the actual
dependent binding addresses; `grammar_binding1` identifies the second grammar
branch. `raw_off_history` proves that outside the existing raw suffix memo
event, no address with that seed suffix is an earlier adversary query.
The law is joint and unnormalised, not a claim of independent public answers.

`ProverCommitPublicCoins41` normalises public answer positions to the values
retained in the conditional context, leaving their independent spare coins
unused. It proves causality, the conditional table law and actual read
agreement. Public reads need memo coherence; only private positions require
freshness and first-occurrence separation. `ProverCommitMixedReads41` also
proves agreement with consistent repeated reads. These are generic read
agreements; concrete private-derived hit/pair bounds and successful source
continuation transport remain to be instantiated.

`ProverCommitBindingErase41.opened_log` proves that substituting both public
binding answers leaves the entire ordered verifier commitment opening log
unchanged, for every opened root, leaf and node. It also permits arbitrary
changes to all three secret slots at this local address boundary. No claim
about whole proof equality follows from that local result alone.

Accepted focused targets: J9195 `ProverCommitPublicPrefix41` (1.91 s,
4,162,116 KiB); J9193 `ProverCommitMixedReads41` (1.79 s, 4,154,696 KiB);
J9197 `ProverCommitPublicCoins41` (1.79 s, 4,158,316 KiB); J9198
`ProverCommitBindingErase41` (1.81 s, 4,156,388 KiB). All exit 0, zero swaps,
standard axioms only. Rejected drafts J9190, J9192, J9194, J9196 are retained;
J9191 is an accepted predecessor of J9195. MixedReads will be rebuilt in the
final dependency audit because PublicPrefix was subsequently extended.
No old HitFresh theorem is falsely claimed discharged on the new carrier.
