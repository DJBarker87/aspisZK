# Collision-qualified and adaptive-statement soundness reduction

The three maintained proofs in `../../lean` passed focused Lean 4.32 checks.
The raw source snapshots, compiler logs, time logs, import pins and receipts
are retained here. Six axiom reports use only the standard Lean axioms.

`AllAddressFiatShamirOutside` replaces unconditional terminal D3 with D3
outside the same collision event used for decoder recovery. The result is
`Qtot * maxErr + κ(Qtot)`: that event is charged once, not again at D3.
`AdaptiveStatementFiatShamir` proves this bound when the prover outputs both
the public statement and proof after its oracle queries; no finite statement
space or union over statements is assumed. `AdaptiveMembershipSoundness`
identifies the specification-choice extractor failure with the absence of
a relation witness, obtaining the adaptive membership-soundness bound.

These are reduction theorems. Decoder injection, chain density, concrete
terminal D3 outside the collision event, the event's probability and the
whole-experiment query bound remain explicit premises. No efficient extractor,
100-bit concrete bound, source correspondence or privacy theorem is claimed.

The existing first-read union bound and finite-support lazy-oracle law are
reused. Each job used one NUC Lean process, MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0, TasksMax=128, `-j1 -M5000 -DElab.async=false`, timeout300.
Receipts record base revision, exact changed-source/object hashes and paths.
All successful jobs exit0 with zero process swaps. Import-resolution failures
remain in the pinned NUC attempt directories; no broad replay was performed.

| Target | Process wall | Peak RSS KiB | Axiom reports |
|---|---:|---:|---:|
| AllAddressFiatShamirOutside | 0:01.27 | 1,806,372 | 2 |
| AdaptiveStatementFiatShamir | 0:01.34 | 1,819,868 | 2 |
| AdaptiveMembershipSoundness | 0:00.84 | 1,810,296 | 2 |
