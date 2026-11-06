# NJY certificate inventory

NJY-RT149 (ReviewedTranscription, option-A RECLASSIFICATION): safe Rust NJQ_identity::decode_ref to NJQ_Identity.reference. Source correspondence: width guard -> Slice.len guard; magic/header/version -> NCX_Reference.magic and index; reserved[5..8]/[108..112] -> bounded NJQ_Read reads; LE asset104 -> U32.from_le_bytes; P canonicality -> 2147483647 bound; returned pool/mint/token/domain ranges8/40/72/112 -> matching natural reads. Full Err variants and ordering retained. Existing NJQ_Identity.source proves reference=model for every slice. NJY_Identity.source imports it, rather than duplicating its proof.

NJY-RT201/203 (pending complete native packets): NJQ hand references and NJQ_Entry/Registry.reference preserve length, ordered header/reserved errors, entry status conversion, every record coordinate, validator full Result and final Ok. Segment _SOURCE.json files pin the exact frozen body, constructor, prefix and literal suffix; transformations are explicit. These items extend ReviewedTranscription under (ay), not a new runtime or cryptographic assumption.

Every new top theorem prints its full statement and #print axioms. Admission requires standard axioms only, NJW+NJQ+headline coherent import, NFX exit0 and raw ax2. No row is credited merely because a reference equation compiles.

Final source review adds NJY_Install.actual_slots for direct registry31/entry32 only. NJY_Install.digest_error_frame preserves digest/error43/44 and wrapper48/49. NJY-B1 rejects direct raw master/checkpoint installation at48/49: those slots have ProgramError/Box wrapper signatures, while assigned raw helpers return full account-format errors. Native helper packets are not wrapper packets. This boundary is recorded, and no wrapper or parent is promoted. The second (and last) combined audit is justified by this new installation source; the first coherent audit is retained.

## Full reference correspondence

|Frozen Rust fragment|Hand Lean reference/model association|
|---|---|
|Checkpoint width/magic/version/lane/digest-encoding guards|NJQ_Header.reference/source; wrong-width Total.Cut rejects before payload reads|
|Checkpoint zero predicate at176..192|NJQ_Reserved.checkpoint_value, NJQ_Library's pure finite any semantics; native ONE-step K010/K011 reused|
|Checkpoint master8..40 and domain40..72, required nonzero checks|NJQ_Checkpoint.masterBytes/domainBytes; bounded reads in source, native head full pair Result|
|Digest80..112 and every mapped AtomicError|NJQ_DigestPort.source, CLOSED digest146; native argument and full map contracts, no SHA/field multiplication|
|Checkpoint lane112+8*k, store then capacity test|NJQ_Words.coordinate/step_argument, NJY_WindowStep.frame/source, NJQ_CheckpointTrace.initial and NJQ_ArrayAll.native_result; post-array retained even on Err|
|Checkpoint bump7, sequence72..80, root, all eight lanes|NJQ_Checkpoint.record/source; exact complete constructor and reversible NJQ_Carrier.checkpoint_result|
|Master header, reserved50..64/312..320 and format8..40|NJQ_Header/Reserved/MasterBinding laws, exact source head contract; any terminal value is internally discharged, not a runtime parameter|
|Master Boolean49|Exact0/1/error split in NJQ_Master.reference/source and native head|
|Master identity64..208, policy208..312 and source order|Full input windows144/104; NJY identity149 and CLOSED policy150; complete map_err Identity/Policy and abort-prefix clauses in NJQ_ChildTotal/MasterCut|
|Master eight words320+8*k|Native window/one-step contracts plus NJQ_Words.coordinate and NJQ_MasterTrace.initial; arbitrary pre-state frame, no whole-buffer native loop|
|Master bump7/mask48/has49/next40..48 and child records|NJQ_Master.record/source and full native constructor/suffix; CLOSED validator157 applied internally to SAME record|
|Registry width/header/reserved, flags5/bump6/keys8,40,72/generation104/delay112|NJQ_Registry.reference/source and RegistryCut.complete_record; all fields in native constructor contract, validator208 complete Result in Total|
|Entry width/header/reserved184..192, status5/version6/bump7, keys8,40,72,104,152 and slots136/144|NJQ_Entry.reference/source and EntryCut.complete_record; CLOSED status192 executes in constructor; validator206 full Result in Total; every InvalidStatus/error arm retained|

Native segment sources/manifests are exact frozen contiguous fragments with only explicitly recorded segment inputs/outputs, child-result boundaries and loop-window factoring. They are neither emitted Aeneas bodies nor evidence from an unrelated rewritten parser. Source-to-cut and reference-to-Lean correspondences remain the reported ReviewedTranscription item under (ah)/(ay), never a new axiom. All internal call domains, full error constructors, read/cast/unwrap bounds and loop frames are checked on the model side and by the paired native segment contracts.
