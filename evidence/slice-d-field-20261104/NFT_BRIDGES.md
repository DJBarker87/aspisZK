# NFT field-helper bridges

**3 functions / 4 new D occurrences CLOSED under the unchanged NFK admission semantics plus additive NFT gates. Driver OPEN; deployed 100-bit per-attempt target not yet established.**

`NFT_certify.py` imports NFQ's unchanged validator helpers and NFK's certificate checks/materializer/row checks/admission. It starts from NFQ's hash-checked composed ledger. It never writes NFQ inputs or another worker's directory. CLOSED callee packets alone do not close a caller.

| Function | New CLOSED occurrences | Native / control | Model root |
|---|---|---|---|
| CM31::write_le_bytes | TX2:008 | K006/007 value; K016/017 frame; K001/002 exact KMX copy controls | NFT_Bytes.cm_value; NFT_ReferenceEq.cm |
| QM31::write_le_bytes | TX2:024 | K008/009 value; K018/019 frame; K003/004 exact KMX copy controls | NFT_Bytes.qm_value; NFT_ReferenceEq.qm |
| WideExact::new | TX1:055, TX2:037 | K012/013 complete record; K010/011 exact KMX record-copy controls | NFT_WideNew.source, canonical_source, reduce_val, reduce_lt |

The writers admit every raw limb, on uniquely borrowed output windows of exactly 8 / 16 bytes, the widths their actual callers pass. Native guard-window checks prove the same selected byte inside and outside the write region on arbitrary prestates. Real callees execute, with no stub_verified. The emitted-model laws retain checked slicing, copy and writeback. Static receiver resolution excludes the inventory's WideExact encoder alternative at CM31 and its spurious QM31 self-recursion. Constructor canonicalization admits all raw u32 limbs and proves every modulo output and bound.

E002 is the safe-reference extraction under NCO pins; its generated files compile unchanged and NFT_ReferenceEq identifies the exact complete byte arrays. L021's optimized driver passes all eight planted/mutation fixtures and raw-walks twelve roots using the byte-identical NEP walker. Every accepted root has standard axioms only. CM frame's arbitrary-tail model law additionally passes L023; it is supplemental until included in the next raw audit.

Excluded: K005 mutable-slice contract timeout, E001's signed-shift extraction mismatch, failed elaborations including automatic sorryAx output, and L015's generated bv_decide axioms. The replacement L017 is symbolic bit extensionality with propext/Quot.sound only. No excluded result is admitted.

Trust retained/reclassified: P6/D188 native contract semantic transport option A, root physical carrier/ABI and uniquely borrowed buffers, compiler/library/Aeneas/source-to-ELF interpretation, and the accepted runtime rows. No premise retired, metric/privacy/two-transaction change, shipped source edit, ELF rebuild, deployment, key operation or push.

Other prepared/passing support is not yet a CLOSED row. In particular square K020/021 and L024 await their source-site association and next raw audit. WideExact::neg K014/015 lacks its complete coherent model/port packet. Full remaining-member details will be maintained in NFT_REMAINING.md.
