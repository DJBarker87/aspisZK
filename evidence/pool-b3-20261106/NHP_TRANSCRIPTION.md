# Reference/source correspondence

No (ah) closure is booked. Guard uses the ordinary extracted-reference NCO route, with unchanged frozen body.

| Source | Reference/model correspondence | Evidence |
|---|---|---|
| processor.rs:2619–2624 | height != TRANSACTION_LEVEL_STACK_HEIGHT rejects with CpiInvocationForbidden; reference height==1 and explicit native Result arm/code predicate | K028/K029; E001; NHP_StackLaw.result/exact_reply/forbidden_error |
| error.rs From<PoolV1ProgramError> | Custom(error as u32); coherent emitted conversion is Custom(read_discriminant error), every54 valid constructors | reused NHC_K078/K079; NHC_ErrorConversion.result; NHP_ConstructorPackets.exact_arms |
| history.rs:52–64 / master/checkpoint prefix | owner first; executable/writability next; master/checkpoint signer then borrow | NHP_AccountPrelude; local native rejection cuts only |
| lane prefix | stored-bump borrow before signer/address; same metadata gate | NHP_LanePrelude; native failed-borrow cut allows either signer |

The last two rows are model prefix laws and bounded physical observations, not full decoder/body or AccountInfo refinement. The E001 failure from NHC is retained by citation; transparent full decoder or reviewed (ah) body and native positive-path packets remain required. No manual transcript is silently promoted to emitted code.
