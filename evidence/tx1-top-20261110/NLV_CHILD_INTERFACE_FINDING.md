# NLV-F2: sibling087 is source/value only

Read-only committed NLR bd1898215e9 explicitly marks RowSpec137 and RowSpec087
SOURCE/VALUE, with physical resources absent. These MUST NOT be supplied as the
full child packet. L075 refused a stale source hash before copying any object.
Refreshed imports use successful NLR_L083/L084 snapshots, retained with hashes.

NLV_PreparePacket names this interface SourceRowSpec_087. It is source/log
support only. NLV_RowSpec087 defines the strictly stronger resource target:
full source/value clause AND one actual12-occurrence resource chain, every
Result/Err/abort prefix, scratch owner/value/writeback and exclusive-release,
logical allocation/view payload/lifetime/disjointness, SAME semantic/claims
owner/payload, returned Prepared Box ownership, cleanup and external framing.
It is UNPROVED and must be reviewed against the ledger before use. No resource
or native087 root exists. NLV does not replace that obligation with the weak
source clause, and emits no094 root. The full-resource interface itself must
be tied to the actual frozen heap/ABI through existing P6, not a chosen witness.
