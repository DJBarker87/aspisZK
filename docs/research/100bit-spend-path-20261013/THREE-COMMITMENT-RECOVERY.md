# Recovery for all three commitment roots

The finite-table recovery argument now covers C1, C2, and the folded-word
commitment. It also translates its byte-level collision alternative into
the same finite-oracle collision event used by the duplex development.
This is a checked recovery interface, not a complete knowledge or spend
security theorem.

`ThreeCommitmentRecovery` proves exact recovery of each accepted leaf's
packed bytes and 32-byte salt from the earlier canonical query records,
provided the appropriate commitment frame was read in that prefix and
three specified bad events do not occur. The proof reuses the existing
finite lookup, canonical-query consistency, literal Merkle evaluator,
first-read target bounds, and duplex collision theorem.

| Commitment | Leaf tag | Packed bytes | Root location in commitment hash input |
|---|---:|---:|---|
| C1 | `0x71` | 480 | Last 32 bytes of the public initial frame |
| C2 | `0xf1` | 128 | Last 32 bytes of the 71-byte row-2 frame |
| Folded word | `0x72` | 128 | Bytes 38 through 69 of the 294-byte row-30 frame |

`CommitmentRootFrames` proves these target-reader roundtrips. The C2
prefix is `state32 || 00 a2 01 20 00 00 00`. The folded prefix is
`state32 || 00 be 00 01 00 00`, followed by the root and 224 response bytes.
The source sites and hashes are recorded in
[COMMITMENT-ROOT-SOURCE-PINS.md](COMMITMENT-ROOT-SOURCE-PINS.md).

Only two root readers are needed: the trailing 32-byte reader covers C1
and C2, while the offset-38 reader covers the folded root. The existing
finite-family theorem bounds their combined target event by
`2*Qtot^2/2^256` in its stated full experiment. The child family separately
has eight readers. These readers deliberately accept more byte strings
than the protocol parser; this enlarges the charged event and does not
replace strict protocol parsing.

`CanonicalMerkleCollision` obtains two distinct canonical oracle addresses
from a byte collision and proves both were read. It then applies
`FS2.Duplex.noColl_injective`. `CanonicalBoundRecovery` combines that result
with the generic root and child target argument; each specialized theorem
excludes exactly those three events. It adds no byte-hash consistency,
collision-resistance, or root-availability assumption.

## What still needs connection

The caller still supplies an actual prior trace, a read of the appropriate
frame, acceptance of the literal opening program, and a distinct-read
bound. Choosing that prefix at the correct commitment time remains
essential. An arbitrary later prefix would not establish that the word
was fixed before the challenges.

This original checkpoint charges events on `pre ++ openingTrace`. The later
[causal stability checkpoint](CAUSAL-COMMITMENT-STABILITY.md) permits
intervening queries and other openings in a common full trace, and proves
the entire recovered function is fixed before each literal frame read.
It also checks a common hash-event bound of `12*Qtot^2/2^256`, including
the duplex event without counting the trailing-root reader twice. Actual
protocol/source composition and final ledger instantiation remain open.
Rust path indexing, folded-tree padding, field parsing, and checkpoint
provenance still require correspondence. Efficient candidate extraction,
the causal knowledge classifier, and the privacy simulator remain open.

## Evidence

Eight changed modules compiled individually on the pinned NUC cache,
followed by `R1ThreeCommitmentCheckpoint` once. The checkpoint exited 0 in
0.79 seconds with 1,798,836 KiB peak RSS and zero swap under 4G/6G/zero-swap
limits. All 28 public axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

Base revision: `eac8ca7d792be9438200ec839b30102a5204881d`. Checkpoint source:
`88cfcec4a6869e96c5092098ddfc0f11525271e189b1735f9a76fb1cc1debb03`.
The sealed `evidence/lean-three-commitment-20261014/` bundle preserves all
19 attempts, including 10 failures, their exact sources, receipts, and
logs. Root reviewed theorem premises and verified all source and object
hashes, resources, runner pins, and the unchanged runtime fingerprints.
