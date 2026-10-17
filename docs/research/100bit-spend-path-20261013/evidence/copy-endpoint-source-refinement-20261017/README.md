# Actual Copy endpoint execution

`AspisR1.CopyEndpointExact.endpoint_success` derives every actual selector-row read, array read, checked arithmetic operation and array store in the sealed indexed candidate's Copy endpoint function. Both returned arrays are canonical. Their decoded cells equal `R0P.copyAccumulateEndpoint` on the same source arrays, endpoint, tag, scalar weight, pattern array and selector arrays. No intermediate operation success is assumed.

The generic `ArrayUpdateCanonicalExact.update_success` proves actual checked update success, canonicality preservation and an exact raw-cell `Function.update` frame. The endpoint proof reuses existing selector, scalar multiplication, lift and QM31 arithmetic lemmas and computes the model endpoint directly from the source descriptor. Descriptor row/slot/pattern bounds, canonical input arrays and canonical tag remain explicit; generated-registry discharge and the full link fold are separate obligations.

`CopyLinkBitArithmetic` additionally proves the actual checked shift/mask/narrow sequence returns the selected bit, and checked one-minus-bit returns its complement. This supplies the two bit cases for the subsequent link-weight source proof; it does not by itself prove the full weight function or registry.

Exact source declarations come from Funs04fc… and Types60cf… with the source manifest retaining full pins and block hashes. This remains the indexed candidate source boundary: full production extraction correspondence, the complete composition caller, runtime/custody, privacy and the final 100-bit accepted-spend theorem are open.

Focused NUC checks all exited0, with zero process swap, under MemoryHigh4GiB/MemoryMax6GiB/MemorySwapMax0. Update:1.226s/2,959,948KiB; endpoint source:1.650s/4,013,164KiB; endpoint behavior:2.152s/4,016,320KiB; bit arithmetic:1.178s/2,573,464KiB. All four exported behavior axiom reports contain only standard axioms (the generic update needs propext/Quot.sound). Receipts retain exact command, source revision, source/object/import pins, time, memory and axioms. No broad replay or dependency rebuild was run.
