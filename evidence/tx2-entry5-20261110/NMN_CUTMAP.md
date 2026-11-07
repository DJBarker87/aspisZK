# NMN cut map under (bl)

Target not yet established; ledger24 baseline 581/0/18. Frozen candidate.rs327–331.

| Call | Recorded arguments | Reply / havoc | Closed Lean root |
|---|---|---|---|
| parse_shape(proof) | proof pointer/length through proof allocation's harness-local UnsafeCell context; both alternate allocations have the same valid layout | all 3 Variant successes and all 8 deployed Error variants; no &mut arguments | NLE_ParseInstall.parse / success |
| mark(None,Parsed) | Parsed asserted in exact-signature cut; deployed None is literal in parent call | unit; no &mut arguments | NHV_ReleaseOps.mark |
| tx2_common(public,proof,checkpoint,hash,None) | pointers/lengths through H's already-received local data pointer | full Result<(),Error>; no &mut arguments | NLT_CompleteRoot.root |

Planned native relation: actual parent returns parser Err unchanged, otherwise common reply unchanged; same arguments at each reached call; no parent account writes or return-data emissions between calls. All buffers retain original allocations and arbitrary bytes at 1880/57607/1768. Parser response is independent of buffer contents in native cuts; its CLOSED law is instantiated later in Lean.

## (bl)(4) classifications

- The common child's internal allocations are fresh. Allocator internals are excluded under (bl)(3), with existing allocator/std trust retained. No four-cell substitute heap is a certificate.
- Child internal digest/return-data events are passed through as an opaque ordered child stream. The parent has no such event between the three calls. Common's exact stream comes from NLT, including C04 stopped prefix.
- A stopped child is nonreturning panic with its prefix only. No returned Result, cleanup, post-abort heap or suffix is claimed. SBF's absence of catch means no extra propagation fact is required by (bl)(3).
- No &mut formal arguments occur in any of the three signatures. The required byte havoc set is therefore empty at this parent boundary. Harness-local logs are instrumentation, not fabricated account state. Controls must still check a deliberately added observable write rather than calling four artificial cells the common footprint.
- Observer is deployed literal None. No function-pointer comparison, arbitrary callback, writable static or Option<fn>-dependent success claim is admitted. Marker phase is checked without inspecting an Option value.
- 57607 follows from SAME successful parse. Public<=1880 and Root0 concern 064's own inputs and are recorded as 241 caller clauses. NMF supplies the accepted headline occurrence outside the existing charged collision event, never an unrestricted failed-prefix fact.

All entries remain planned until native controls and Lean gates pass.

## Native domain completeness classification

The native certificate uses original57607/1768 proof/checkpoint allocations. NMN_064.Domain explicitly records those exact extents, public<=1880 and Root0 as064 OWN-input predicates under(bf)(2). No all-length native claim is made.241 must discharge both exact extents from SAME getter/checked_add/range facts (NLW_StartScope/NLM_ReadExtent) and public bound from encoder1880. Parser success independently implies57607 at the common call. These clauses are never endpoint or success hypotheses. All original bytes are arbitrary, including malformed headers.

## Current native receipts

K014/K015 PASS on actual parent returning/rejection paths. K016/K019 ignored-reply controls FAIL; K017/K020 alternate-allocation argument controls FAIL; K018/K021 required local-log write omissions FAIL. K022 common panic branch reaches the intended panic (not a passing-return theorem);(bl)(3) provides no-catch propagation, retaining only child prefix. K023/K024 stability PASS/FAIL agrees with original names. K025/K026 canonical exact KMX pointer checks PASS/FAIL. All13 runs have identical current parent/stub source hash in NMN_CONTROLS.json. No writable static, function-pointer value assertion, field-product proof, own copy stub, or claimed post-abort world.

Parser log is reached through its ORIGINAL proof allocation's data pointer: NMN_Frame contains an UnsafeCell local record preceding the proof subobject; subtracting the known field offset stays inside that same allocation. Both normal and alternate control frames have this layout. The shared proof slice never overlaps the UnsafeCell log. Pointer/length assertions occur after return. Common logs the exact three original slices through the received generic H data pointer. Marker has unit reply/empty footprint; its Parsed argument is checked at the exact-signature cut. The deployed literal None is fixed syntactically and never compared; NMN_Observer supplies the erased model phase law.
