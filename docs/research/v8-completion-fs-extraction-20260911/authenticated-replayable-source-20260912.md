# Authenticated replayable source — 2026-09-12

`lean/ExtractionCollectorAuthenticatedReplayable.lean` extends the live
source/OOD/gamma/middle/later transcript with the selected same-body Merkle
leaf/node verifier. Authentication starts only after the actual live sampler
has returned a valid, distinct length-22 query list. The typed schedule is
constructed from that list; the verifier consumes the same returned body and
the roots fixed at the earlier chronological cuts.

On success, `successful_constructs_merkle` constructs the functional
`SuccessfulMerkleRun`, both root equalities, and inclusion of every leaf and
internal-node hash input in the combined final log. No Merkle success object,
opening-call inclusion, or independent query schedule is a theorem premise.
Sampler invalidity and parse/root/Merkle failure remain aborting branches.

This is not complete verifier acceptance. It does not yet execute the
relation terminal, connect the source-produced chronological C1/C2 answer
prefixes to the authenticated quotient values, construct a checked payment
witness, or refine the mutable Rust verifier. The root cuts are an explicit
input here; `FSAuthenticationSuffix` is their existing chronological producer.

Focused NUC evidence used Lean 4.32.0 with `MemoryHigh=8G`, `MemoryMax=9G`,
`MemorySwapMax=0`, `RuntimeMaxSec=600`, `-j1 -M8192`. The successful final
compile exited zero in 3.07 seconds, peaked at 6,753,804 KiB RSS and used no
swap. The imported historical first-party cache remains a development cache,
not a fresh dependency-closure certification replay.

