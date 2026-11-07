# NMP stub inventory

No field multiplication stub is used. No field product or SHA body is proved in
Kani. All field values in free child replies are constructed as typed arbitrary
limbs; WideExact's cfg-only constructor covers all bits of its Rust fields.
The actual wide_view executes only fixed slicing and 32-byte field decoding.

| Stub | Role and state |
|---|---|
| Prefix::parse | free Err or typed Prefix; source-backed-view constructor limitation in CUTMAP; CLOSED parser law composed later |
| public_transcript | full runtime state32/row8 and any Error; LoggedHash pointer is the local instrumentation channel |
| begin | any Challenges or Error and every runtime transcript field overwritten; omission control at subsequent finish |
| verify_finish | arbitrary full owned Verified or Error, with real claims Box; no child law assumed in Rust |
| heap::filled | fixed14759 fresh Vec and primitive zero initialization; allocator internals reclassified under existing std/allocator by(bl)(3) |
| expand_semantic / expand_values | independent arbitrary byte for every returning mutable output cell; no canonicality or child relation assumed |
| verify_observed at prepare | arbitrary full owned Verified or Error; per(bl) independent of137 closure |
| Prepared::new | arbitrary full Prepared or Error and every g cell overwritten;179's law remains a Lean composition obligation |
| copy_nonoverlapping | ONLY exact KMX_copy_stubs.patch; pinned SHA in NMP_NATIVE_SEED and source gate; K007 positive/K008 matched failing control |

No stub_verified, proof_for_contract or new function contract is used, so no
unvalidated contract return shape is admitted. No writable static or
Option<fn>-dependent assertion is present. Deployed None observer and family
rename-stability calibration are tracked separately; no rename repairs a verdict.
Full Rust signature/domain and callee-root inventory is in NMP_CHILDREN.json.
Kani passes here remain local cut/projection support until all remaining native
frames, full-type cases and SAME-child laws have been composed and gated.
