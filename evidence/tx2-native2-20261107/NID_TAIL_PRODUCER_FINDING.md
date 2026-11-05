# Tail canonicality is an actual producer/history boundary

TX2:065 remains OPEN. No stronger root precondition is adopted here.

Frozen verifier.rs::resume uses proof only as a digest input; its scalar readers
consume checkpoint bytes. Its successful canonical Prepared/Accumulator fields
therefore do not themselves certify that proof[7527..7751],
proof[7783..8007], or proof[8007..10055] contains canonical field encodings.
A hash binding identifies the same bytes; it is not a canonicality theorem.

NID_TailView.produced derives the actual SAME View and all224/224/2048 widths.
NID_FinishAlpha derives the primitive Prepared finish domains from the SAME
reader result. Neither fact is substituted for7/7/64 canonical windows.

The missing producer is the actual first-transaction canonical_scan and its
transport through the saved-checkpoint/history/carrier chain into this proof.
The pinned NHO ledger still marks TX1:084 canonical_scan OPEN. The authenticated
Pool route requires the SAME writer/scan/history evidence; native resume success
alone is insufficient. The public tx2 route has its own scan before tx2_common.
Their distinct caller obligations must not be conflated.

Next deliverable: a CLOSED source/native canonical_scan packet, the actual
successful scan occurrence on the first transaction's SAME proof, and the
existing NGS/NGR carrier/history transport applied to that occurrence. This is
a slice boundary, not a proposed new runtime/cryptographic trust assumption.
No standalone malformed-proof acceptance or hash-collision claim is made.
