# NJN reusable-law register

**Target not yet established. No complete reusable SDK certificate is submitted.**
These are candidate statements and supporting results, recorded once for reuse;
no caller is licensed to assume a pending statement. Counts remain 438/0/161.

| Law | Exact statement and caller domain | Native association | Lean root / status |
|---|---|---|---|
| Borrow acquisition | On a live admitted 3/7-account heap, valid account index, same allocated Rc/RefCell and fresh token: shared succeeds iff 0≤counter<MAX, exclusive iff counter=0; successful typed guard refers to that same payload/counter, failure is AccountBorrowFailed with unchanged heap. Only selected counter/token changes. | NJN_sdk::shared/exclusive are exact one-call wrappers around frozen AccountInfo methods; safe constructed native states and controls are supporting evidence. Direct SDK annotation and universal typed carrier association are not proved. | NJN_GuardModel.shared_ok/shared_error/exclusive_ok/exclusive_error/acquire_frame. Hand model, not extract(f_ref). |
| Deref/move/drop | A valid live guard keeps its descriptor and cell when moved or discriminated through Result. Deref returns that cell's full slice; exclusive deref permits writes within bounds. Consuming shared token decrements current same-cell counter; consuming unsplit exclusive at -1 restores zero. Other cells/tokens/metadata and payload are framed. | Actual typed return, movement and Drop execute in native wrappers. Counter observation reads pinned native RefCell layout; never constructs a guard. Full Ref/RefMut correspondence remains open. | NJN_GuardModel.drop_consumes/drop_other_token/exclusive_drop_zero/drop_payload/drop_frame/shared_roundtrip/exclusive_roundtrip. Support only. |
| Exclusive-copy ABI | A valid exclusive token, source/destination bounds, equal lengths and disjoint source: copy the full supplied source into the SAME guard cell, preserve all other cells/metadata/tokens, Drop retains written payload and restores counter. Three/seven-account handle association is required separately. | One arbitrary byte window plus outside coordinate in the 1768-byte payload is the native split; exact KMX patch required. No whole NJD_K038 rerun. | NJN_GuardModel.copy_range/copy_range_outside/copy_range_frame/copy_range_live/copy_range_drop, using canonical KMX_CopyMeaning.loop_spec/copy_frame. Native whole-layout ABI pending. |
| Clock get | Actual Clock::get initializes its output allocation, forwards its address to the runtime call, then returns all five output fields on status0; otherwise exact ProgramError::from(u64), including BorshIoError("Unknown") and truncated custom codes. Exact syscall status, output-region identity and ambient frame required. Successful slot uses RuntimeClockSlotBinding only after success. | NJN_conversion tests the actual concrete converter via exact wrappers. Local-record association to the actual Clock syscall/get body is missing; host and deployed branches must be distinguished. | NJN_ClockModel.success/failure/builtin/custom_zero/custom_other/region_frame/slot_binding. Pending emitted-reference and native ABI association. |
| PDA syscall | Validate seed count≤16 and each length≤32 before the call; retain exact ordered seed descriptors/program id/output allocation; forward raw status and bytes; status0=Ok(bytes),1=InvalidSeeds,2=IllegalOwner; unsupported statuses abort in PubkeyError::from. Frame preserved. Address bytes are quantified op38, with no value law. | NJN_conversion::pda_convert calls actual SDK conversion for status0..2 with matched corruption control. Exact deployed syscall callsite remains open; host SHA/curve body is not a substitute. | NJN_PdaModel.ok/invalid/illegal/unsupported/rejected/arguments_frame. Pending emitted-reference and native syscall association. |

The single reference extraction covered twelve roots over owned Heap/Account/
Cell/Guard and the complete reply carriers. Charon succeeded, Aeneas failed at
guard drop (InterpBorrows.ml:2731), emitting nothing. Thus **none** of the
hand-model roots proves extract(NJN_reference)=law. No existing scalar NJH
emission is relabelled as a full carrier emission. Source fingerprints,
commands, source revision, wall/RSS/swap and axiom lines are in NJN_ATTEMPTS.

All current mathematical roots import with NJK_COMBINED_IMPORT and the headline;
the final raw ax2 and NFX-method scan gate is recorded in NJN_AUDIT.json. A clean
audit certifies these statements, not the absent native/reference associations.
No assumption is discharged or added; P6/D188 option-A transport is retained
reclassification. RuntimeCpiReadonlyEntry7 and a PDA value trust row are unused.

Final scoped additions: K065/K066/K067 certify the actual 1768-byte exclusive
copy window and its outside/metadata/drop frame against value/frame mutations.
K068/K070 pass/fail on the actual Borsh conversion's arbitrary byte coordinate
in a direct interface; K024's full contract is still open. K018/K069 pass/fail
on actual Clock::default initialization, five zero fields, native40-byte zero
region and alignment8. None supplies the missing Clock syscall association,
full three/seven-account ABI or extracted reference equality. K016/K017's
large-payload conflict interfaces timed out and are not candidate laws.
