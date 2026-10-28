# exact<8>/<32> on the reached ASJA call sites — CLOSED

Frozen `pair_terminal::exact`: native try_into plus map_err(WrongLength). K006 and K007 prove its exact Result at widths8 and32, on all byte arrays/slices of length<=64. Wrong widths return exactly WrongLength. On success every returned byte equals the corresponding input byte (an arbitrary index is checked). No canonicality premise or digest encoding is used, and the actual native helper is called unchanged.

`NBH_Exact.source` (L021) proves the adopted helper for arbitrary N and arbitrary Slice U8: exactly the SAME byte list iff its length equals N, else WrongLength. `accepted_bytes` and `rejected` expose both directions. Axioms: [propext, Quot.sound]. Exact byte arrays and all Result distinctions are retained under the existing P6/TrustedStd slice/array conversion contract.

The native gate's length<=64 is not imposed on a caller arbitrarily. NBH_ExactCallerDomains.json mechanically inventories EVERY actual ASJA helper call after the dominating688-byte length guard:21 static32-byte ranges and one8-byte range, all in-bounds. Every actual call therefore establishes both native gate widths and the length bound. Rust's checked source slice and the retained library range interpretation supply these identical slices; no independently chosen range or successful child is assumed. This closes this helper on ALL reached specializations of the assigned codec, not a native theorem about every possible const N / unbounded foreign slice.

The enclosing ASJA decoder is still OPEN at canonical digest decode and full ordered decoder/result association. This helper closure removes no headline premise or runtime/library trust item.
