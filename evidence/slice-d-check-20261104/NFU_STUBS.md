# NFU stub and trust table

No field multiplication is executed in a Kani proof and no new field-product stub is used. No LPh product-law pairing is claimed. Field product obligations inside the cited CLOSED NFG push packet retain its existing Lean laws; NFU never reproves them in Kani.

| Substitute | Domain / obligation | Status |
|---|---|---|
| Exact KMX_copy_stubs.patch, sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 | T:Copy; exact selected pointer/slice window; fixed-value and header copies; existing KMX_CopyMeaning value laws, with K024/K025, K040/K041 and each copied-shape matched control | Used only with exact adopted bytes; no private copy stub |
| unreachable_validation | Malformed parse_record header must return before validation; stub asserts false if called | K015/K063 guard fragment only; parser OPEN |
| unreachable_parse | parse_record_at short get must return before parsing; stub asserts false if called | K021/K053 guard fragment only; parser-at OPEN |
| finish recorded_push local record | Actual typed EbyKDot, full unconstrained Result<(),()> and declared nine-word receiver mutation; canonical SAME E input, arbitrary raw scalar/count/old fields and valid unique receiver as in CLOSED NFG public push packet | Candidate one-step certificate only; source/model/loop/new/finish/aggregate joins OPEN; no composed credit |

All logs and plans are local records passed by mutable reference. No writable static, function-pointer comparison, Option<fn> dependence, or stub_verified caller composition is used in a credited bridge. The only stub_verified use is the matched u8 fidelity denial K010, which correctly fails. Runtime/SDK/allocator/compiler/library/source-to-ELF and P6/D188 option-A transport are retained, not removed. ReturnData/Memcmp owner acceptance is retained; no new trust row is added.
