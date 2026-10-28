# NCO stub/domain table

No field multiplication is executed or stubbed in this pilot. All field
multiplication obligations remain on the adopted Lean-discharged route.

|Stub|Meaning/domain|Use and status|
|---|---|---|
|KMX_copy_from_slice|Exact unchanged KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; equal lengths, u8 Copy|Single-window expansion and decoder controls. K056 positive / K057 negative. Imported KMX_CopyMeaning value laws retained; not a new trust item.|
|KMX_copy_nonoverlapping|Same patch; valid disjoint initialized source/destination regions; u8 Copy|Decoder/expansion and Vec controls. Exact patch files independently hash-checked by NCO_gate.py from K046 onward.|
|KMX_realloc|Same patch; allocation preconditions, preserve min(old,new) on success, old on failure|Vec fidelity controls only; no Vec caller bridge admitted.|
|stub_verified(row_shape)|All u8; complete Option<(tag,size)> equality to safe reference|Final positive, inverted contract and wrong-callsite controls K048–K051.|
|stub_verified(compact_row)|All u8; exact threshold predicate|Final positive/control receipts K052–K055.|
|stub_verified(validate_record_fields)|ONLY payload length32; exact Result, row and index from safe reference|K060–K064. Not a complete leaf contract for the actual parser's maximum3712.|
|stub_verified(parse_record)|Diagnostic row<14, record≤37 (split restrictions recorded per run)|K039/K044 compiler rejection of borrowed returned slice; never admitted.|

All caller domains remain obligations. One-window leaf contracts cannot be
used at row25: NCO_Domains proves the concrete mismatch. No opaque success
stub, unchecked field stub, SHA implementation or function-pointer stub is used.
