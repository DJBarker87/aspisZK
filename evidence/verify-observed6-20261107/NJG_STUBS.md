# NJG stubs

No field operation stub or function contract is introduced so far. No SHA evaluation or syscall value model is used.

`core::ptr::copy_nonoverlapping` -> exact `KMX_copy_nonoverlapping` from evidence/kani-mitig-20261028/KMX_copy_stubs.patch. Domain: live disjoint source u32 and destination word inside MaybeUninit<[u32;348]>, index116*p+i with p<3,i<116; independent initialized frame at j<348 outside selected row. Positive and matched failing control are required under this identical patch/configuration. Paired value laws: KMX_CopyMeaning.loop_spec/copy_frame, NJG_RowWindows.selected/frame/complete. This is the approved mitigation, not a new copy stub; pointer validity and aggregate-write lowering are not implied by those value theorems.

The helper is in aspis-core/r0 only and reaches no verifier crate; deployed verifier feature parity is not claimed for this helper run. Every run retains full resolved graph/features and frozen lock before/after. No Option<fn>, writable static, stub_verified or proof_for_contract used.

Native source-loop decode oracle (NJG_claims_loop.rs.txt) logs actual row/borrowed pointer/length/offset/count on one arbitrary prestate; complete returning Length/NonCanonical branches retained. Its caller-installed decoder147 domain is NJG_ClaimsGeometry.decoder/source_offset. The returned polynomial is arbitrary; actual row write remains native, with complete selected-word and rejection-frame assertions in the result stage. No writable static, Option<fn> or field product. Native request/post/abort-to-StdCalls transport remains open.

## Final reviewed table

| Replacement / oracle | Paired Lean law or exact missing law | Status |
|---|---|---|
| Exact KMX copy intrinsic | KMX_CopyMeaning.loop_spec/copy_frame; NJG_RowWindows.selected/frame/complete and RowPrefixes | Approved mitigation bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; paired controls in every credited configuration. |
| Claims decoder call log, original one-iteration body | ClaimsGeometry.decoder/source_offset; NativeCuts.claimsArgs/claimsResult; actual indexed decoder147 installation remains required | Final pairs K024–027 only have the complete caller error-index domain; no row129 closure. |
| Original driver semantic_round call log | RoundsCompose.complete/site_domain/error_no_suffix/abort_no_suffix; RoundsUnrolled source/ordered; CanonicalPrefix.step | Full child Result returned unchanged; native133 realization/domain join remains open. |
| Fresh finish external-call dictionary | FinishInstall.source and ConfiguredFinish.source; exact actual ordered from_fn, source getter/payload/state/decoder and unwrap implementations installed | Source/model support only; arbitrary protocol function interpretations are not admitted native child packets. |

No field multiplication stub was introduced, so no field stub/theorem/domain pair is outstanding from NJG. No proof_for_contract or stub_verified appears; the per-shape function-contract fidelity controls are therefore not invoked. Runtime digest calls retain exact slices and unchanged replies through the input carrier map; digest values retain the existing runtime trust row. RuntimeCpiReadonlyEntry7 is not used. No allocator or terminal realization is silently classified as std trust.
