# Exact conditional interface

The kernel statement is NIB_ReadToSettlement.read_to_settlement. Its three
success conclusions are DERIVED, not stored in a new premise structure.
The physical plan remains OPEN: callback instantiation and the production
write/borrow frame are not consequences of a model equation.

| Binder / exact statement | Owner / disposition |
|---|---|
| `law : NGK_NFR_PoolReturnData.RuntimeReturnData runtime` | ACCEPTED RuntimeReturnData: for each same context/program and byte list, `1 ≤ length → length ≤ 1024 → read context (write context program bytes) = some (program,bytes)`. The legacy NFO law allowing empty bytes is NOT used. |
| `sameCpi : poolInvocation = emitInvocation` | NHP successors, Pool B item 7. Invocation indexes both program and context; `congrArg context sameCpi` binds the SAME context. This is native provenance, not an accepted runtime row. |
| `selectedProgram : program emitInvocation = selected` | NHP successors, item 6. Actual authenticated registry selection and invoked program, not a free key choice. |
| `noInterveningCpi : readState = runtime.write (context emitInvocation) (program emitInvocation) (S2K.ResultPayload.bytes s).val` | NHP successors, items 7–8, coordinated with TX2 driver. This is the EXACT current Runtime interface's projected-state hypothesis, not a theorem that mere temporal absence of CPI implies it. State here is the return-register projection, never the full account heap. Its physical realization is pending candidate NIB-P1. |
| `emitted : NFY_JHb_Emit.source (fun st bytes => ok (ReturnData.set st bytes)) state s = ok (.Ok after)` | TX2 driver NHT/NHV/NHY: reached successful emit_result on THIS statement/state. S's CLOSED `NFY_NEY_EmitComposed.result_state_effects` is used to invert the actual model child, deriving binding success and terminal validity. S closure alone does not prove the driver reaches that call. |
| `acceptedDecoder : NGK_NFO_ReadModel.run selected (.Ok ()) (runtime.read (context poolInvocation) readState) NGK_NFO_PacketDecoder.run = ok (.Ok authenticated,events)` | NHP successors: actual native accepted read at cap792, instantiated through CLOSED NFV C/(y) cuts, same invocation and live context. Decoder inversion is the existing proved NGK_NFR_RawInverse.accepted_codec, not a new assumption. |
| `checked : validate authenticated.value = ok (.Ok ())` | NHP successors, Pool item9: reached successful `validate_authenticated_terminal_result_v1` with actual request/master/checkpoint/lane, actual model dictionary and actual error conversion. This observation is allowed by the plan; mapping generic `validate` to the production helper is NIB-P2, not silently supplied. |
| `advanced : lane authenticated.value = ok (.Ok image)` | NHP successors, item9: reached successful `next_lane_image_box_v1` on the SAME actual pre-lane and decoded result. Mapping `lane` and `image` to the production helper/image is NIB-P3. No consequence about account writes follows from this alone. |

All type, state, statement, callbacks, image and event binders are universally
quantified fixed values. No existential alternate execution, arbitrary Prop
boundary, native whole-body equality or freely chosen successful output is used.
The callbacks are explicit interpretation parameters; no physical closure credit
is claimed for choosing them. Nonempty/bounded return length is proved as exactly
792 from the SAME authenticated bytes; it is not a new precondition.

Derived: valid terminal statement; semantic check on `ResultAdmission.value s`;
lane success on that value; accepted value/byte identity and four-event trace;
exact emission state; ModelJoin settlement result and ordered child trace;
helper encode/allocation trace with SAME792 bytes. Retained: accepted runtime
rows, P6/D188 transport, SDK/std/allocator/ABI/compiler/ELF realization and all
headline cryptographic/game premises. No premise of deployed is removed.
