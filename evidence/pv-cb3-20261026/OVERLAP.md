# Later sibling overlap

V246/op229 was absent at this worker's 17:29:58 sibling check (head93c41a0ab2).
This worker passed24705 at17:37. The sibling subsequently committed its own
`PV_CB_Op229Source.op229_source` in575f9d5b9b at17:45. Both are candidate source
proofs of the same ledger row. Count V246 once in any combined recount; do not
add this worker's row arithmetic to the sibling's arithmetic without deduplication.
