# NJG stubs

No field operation stub or function contract is introduced so far. No SHA evaluation or syscall value model is used.

`core::ptr::copy_nonoverlapping` -> exact `KMX_copy_nonoverlapping` from evidence/kani-mitig-20261028/KMX_copy_stubs.patch. Domain: live disjoint source u32 and destination word inside MaybeUninit<[u32;348]>, index116*p+i with p<3,i<116; independent initialized frame at j<348 outside selected row. Positive and matched failing control are required under this identical patch/configuration. Paired value laws: KMX_CopyMeaning.loop_spec/copy_frame, NJG_RowWindows.selected/frame/complete. This is the approved mitigation, not a new copy stub; pointer validity and aggregate-write lowering are not implied by those value theorems.

The helper is in aspis-core/r0 only and reaches no verifier crate; deployed verifier feature parity is not claimed for this helper run. Every run retains full resolved graph/features and frozen lock before/after. No Option<fn>, writable static, stub_verified or proof_for_contract used.

Native source-loop decode oracle (NJG_claims_loop.rs.txt) logs actual row/borrowed pointer/length/offset/count on one arbitrary prestate; complete returning Length/NonCanonical branches retained. Its caller-installed decoder147 domain is NJG_ClaimsGeometry.decoder/source_offset. The returned polynomial is arbitrary; actual row write remains native, with complete selected-word and rejection-frame assertions in the result stage. No writable static, Option<fn> or field product. Native request/post/abort-to-StdCalls transport remains open.
