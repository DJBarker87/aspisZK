# Reference/source correspondence

No (ah) closure is booked. Guard uses the ordinary extracted-reference NCO route, with unchanged frozen body.

| Source | Reference/model correspondence | Evidence |
|---|---|---|
| processor.rs:2619–2624 | height != TRANSACTION_LEVEL_STACK_HEIGHT rejects with CpiInvocationForbidden; reference height==1 and explicit native Result arm/code predicate | K028/K029; E001; NHP_StackLaw.result/exact_reply/forbidden_error |
| error.rs From<PoolV1ProgramError> | Custom(error as u32); coherent emitted conversion is Custom(read_discriminant error), every54 valid constructors | reused NHC_K078/K079; NHC_ErrorConversion.result; NHP_ConstructorPackets.exact_arms |
| history.rs:52–64 / master/checkpoint prefix | owner first; executable/writability next; master/checkpoint signer then borrow | NHP_AccountPrelude; local native rejection cuts only |
| lane prefix | stored-bump borrow before signer/address; same metadata gate | NHP_LanePrelude; native failed-borrow cut allows either signer |

The last two rows are model prefix laws and bounded physical observations, not full decoder/body or AccountInfo refinement. The E001 failure from NHC is retained by citation; transparent full decoder or reviewed (ah) body and native positive-path packets remain required. No manual transcript is silently promoted to emitted code.

SDK word reference E002: the26 constant/constructor rows and Custom fallback are mechanically derived from locked package sources; native K069/K070/K071 check the actual SDK implementation. NHP_ErrorModel is a canonical carrier codec/range law, not a silent installation into headline op44. Native residual K104/K105 reaches the actual ?/FromSame path for this producer class; general String/caller frames remain open. No(ah) whole-decoder closure is claimed.

Packer iterations K114..117 use byte-for-byte statement spans from the frozen function, recorded with SHA256. NHP_SeedGeometry is pure index/word-bound support. No copied iteration or geometry theorem is promoted to a complete emitted pack/parent correspondence.
