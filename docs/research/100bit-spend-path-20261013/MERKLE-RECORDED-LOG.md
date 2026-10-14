# Recorded byte logs and Merkle recovery

The recovery theorem now uses strictly parsed records from a literal byte-query
log. It proves that an opening either recovers its exact packed payload and
salt, exposes a collision between a recorded input and an opening input, or
uses an opening input absent from that log whose hash equals a supplied root
or a recorded child. A separate bridge connects the child case to the existing
finite-family first-read event when the log is an earlier execution prefix.

This reuses the [finite-table recovery theorem](MERKLE-TABLE-RECOVERY.md),
`FS.hitsBad_of_first`, the `FS2.Duplex` first-read/table calculus, and the
existing parsed-target density theorem. It does not establish the complete
knowledge extractor or a numerical private-spend security claim.

## Exact statements and premises

`MerkleNodeCodec.parse` reads eight 32-byte children and accepts only when
re-encoding gives the entire original input. Its roundtrip and soundness
theorems retain the `0x18` marker and exact 257-byte node shape.
`MerkleLeafCodec.parse` requires the supplied tag, fixed payload width,
32-byte salt, and exact re-encoding. Its roundtrip applies to the C1, C2, and
folded leaf layouts when their corresponding tag and width are supplied.
These are constructive parsers, not searches over possible preimages.

`MerkleRecordedLog.nodes` and `leaves` filter the recorded query pairs through
those parsers. Their consistency follows from consistency of the input log.
Parser completeness proves that a failed lookup at the hash of a correctly
encoded node or leaf implies that this input was absent from the log. The
lookup may return the first matching digest; the recovery theorem retains a
collision alternative to account for ambiguous digest matches.

`MerkleLogRecovery.recover_or_bad` assumes:

- a finite byte log whose recorded outputs equal the supplied hash function;
- the specified packed width and a 32-byte salt;
- a full slot-indexed authentication path and equality of its computed digest
  with the supplied commitment root.

It concludes exact payload/salt recovery, a cross-trace collision, or an
`AbsentTargetHit`. That last event explicitly contains an opening input absent
from the prior byte log and a hash in the root/recorded-child target list.
`MerkleTraceInputs.inputTrace_node_shape` supplies the node shape needed for
the absence proof; no node-shaped-input premise is added to the main theorem.

`MerkleRecordedTargets.byteLog` projects a bounded-address trace to its byte
inputs and outputs. `target_cases` shows that a target in its parsed-node
table is either the supplied root or a child obtained by one of the eight
literal node parsers from a read address.

`ParsedTargetsPrefixHit.before_of_prefix` proves that an address read in a
prefix precedes the first read of an address absent from that prefix.
`MerklePrefixHit.root_or_child_hit` then uses a consistent `pre ++ post` trace,
its explicit distinct-read bound, a read in `post`, byte-input absence in
`pre`, and target membership. Its conclusion retains the supplied-root case
or places the execution in the already bounded child-target event.

`MerkleChildTargets.mass` instantiates the existing family theorem with eight
child positions. For the stated arbitrary prover/verifier oracle experiment
and its uniform distinct-read budget `Qtot`, it gives
`8 * Qtot² / 256^32`. This is the child-target event only. It is not the full
Merkle binding, Fiat–Shamir, or spend error term, and is not added to a final
ledger here.

## Remaining connections

The supplied commitment-root case is still explicit. The
[root-parser inventory](MERKLE-ROOT-PARSER-INVENTORY.md) identifies reusable
initial-C1 parsing and the C2/folded layout connections that remain. Root
predictors must be tied to the appropriate commitment-time reads before a
full event containment or probability sum is asserted.

The byte-log recovery theorem and bounded-address prefix theorem are not yet
an end-to-end application to the literal Merkle oracle program. In particular,
the shared bounded-address encoding, opening-read inclusion, and byte-hash
consistency must be proved together. `Addr.toBytes` filters `none` entries from
an option-byte vector and is not injective on arbitrary padded vectors.
Consequently, projecting every arbitrary address read to bytes does not by
itself prove consistency with one byte-string hash. A canonical-address
restriction or filtered-log construction is required at that interface; no
such consistency is silently assumed as a universal fact here.

The earlier D2 table-quantifier issue, efficient list decoding and knowledge
extraction, source correspondence, full privacy, and the absolute security
accounting remain open. The conditional Fiat–Shamir bound still includes
its query factor. These local results do not remove it or add work credit.

## Focused verification

The ten changed component targets compiled individually on the pinned NUC
cache, followed by `R1MerkleRecordedLogCheckpoint` once. The combined target
exited 0 in 0.74 seconds with peak RSS 1,797,808 KiB and zero swap, under
`MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`. Its 29 axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`.

The base revision is `3c8e4eb428875e27bf3a061acf2329b61a9d1a59` and the
checkpoint source SHA-256 is
`9d4cbf21f3c020cf9a2eb864aaa7e75e231a1e807fa91275634d5d20dca55609`.
Exact source snapshots, failed attempts, timings, resource receipts, and
compiled objects are retained in `evidence/lean-merkle-recorded-log-20261014/`.
One worker accidentally repeated unchanged FirstHit attempt b as attempt c;
the duplicate is retained and identified as redundant, not additional
validation. No runtime source changed and no unchanged runtime suite was rerun.
