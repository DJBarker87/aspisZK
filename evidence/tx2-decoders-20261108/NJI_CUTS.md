# NJI native cuts

No writable static or Option<fn> observation. Every oracle/log/counter is local. Every native run has strict frozen graph/lock/source erasure, exact KMX stubs, deployed features and owned target. K003/005 use modifies() on the actual V1 validators. K004/006 fail the actual inverted ensures, not compiler diagnostics. No stub_verified interface used.

Policy K009/K010: exact body copied from frozen format.rs::decode_verifier_policy_v1, with ONLY validate_verifier_policy_v1(&policy)? replaced by *log=Some(policy); reply?; reversal is checked by NJI_policy_cut_gen.py. Physical domain104 bytes, arbitrary byte i<32, arbitrary full Result<(),PoolV1FormatError>. Header rejects assert log None and exact first error. Live arm asserts log entered, flags, all three selected argument bytes; Err forwards the exact reply; Ok asserts returned flags and the same three arbitrary coordinates. Readonly input is borrowed; only local log modified. These assertions are the reviewed cut; output success is never an assumed premise. Full-array equality requires Lean extensionality over i, never a copy/equality inference.

K008 timed-out whole-return shape is retired. K009 coordinate shape removes the expected full record and checks arbitrary coordinates, no timeout increase or unchanged replay. K011 source gate failed because a previous owned format sidecar persisted outside the historical incremental upload; the owned runner now restores every known omitted parent from frozen Git after checking the original expected hash. Validation is stricter, no historical pin weakened.

Missing-body decoders201/203: stage cuts follow the same local-record pattern with arbitrary field and byte, every Result constructor and exact first error/status ordering. These are native support until a permitted complete source/model route is audited; a passing probe alone admits no row.

## Final strengthened stage inventory

| Native pair | Source stage / domain | Lean association |
|---|---|---|
|K023/K024|master parent; full record input snapshot/frame; exact policy and8-word any argument logs; all errors and metadata flags|NJI_MasterCut.child_arguments/native_source; NJI_MasterModel.source|
|K025/K026|policy decoder104 original bytes; snapshot/frame; flags and all three arbitrary field bytes, full nine-way reply|NJI_PolicyCut.complete_record/native_source; NJI_PolicyTotal.native_source|
|K027/K028|entry192 original bytes; arbitrary field/byte and scalar, status first-error, full13-way reply, input frame|Support only: omitted emitted decoder201|
|K029/K030|registry128 original bytes; arbitrary field/byte/scalar, full13-way reply, input frame|Support only: omitted emitted decoder203|
|K031/K032|master readonly Iter::next ONE iteration, arbitrary k<=8/exhaustion, original selected/arbitrary words and length frame, scalar capacity comparison|NJI_Any.pure_run/result; NJI_MasterModel.callback; NJI_StdAnyTransport and NJI_MasterIteration.source_association|
|K033/K034|checkpoint IterMut::next ONE iteration, arbitrary k<=8, write-before-reject, prefix capacity invariant, original input and untouched-word frames|NJI_CheckpointLoop.written_step/valid_step/finished/first_error/abort_prefix; support for152 only|
|K035/K036|policy scalar length guard, actual record/error carrier, every usize length|NJI_LengthCuts, NJI_PolicyTotal|
|K037/K038|registry scalar length guard128, actual carrier, every usize length|NJI_LengthCuts; support only|
|K039/K040|entry scalar length guard192, actual carrier, every usize length|NJI_LengthCuts; support only|
|K041/K042|master scalar length guard384, actual carrier, every usize length|NJI_LengthCuts; support only|
|K043/K044|checkpoint scalar length guard192, actual carrier, every usize length|NJI_LengthCuts; support only|

No fake large slices or descriptor/payload mismatch: wrong-length stages operate only on the unrestricted real usize descriptor via existing P7 Slice.len. Thus256/320 and all other wrong lengths reject before reading a payload. Entered coordinate stages execute the original frozen read/constructor bodies with only explicitly logged callee cuts; source reversal checks are pinned. Aborts have no child/suffix log after the relevant guard. KMX copy patch SHA256 is pinned in NJI_FINAL_CHECK.json; all native pass/control configurations validate the same frozen source/graph/lock and retain their own target path. No field arithmetic stub or multiplication proof is used in this lane.
