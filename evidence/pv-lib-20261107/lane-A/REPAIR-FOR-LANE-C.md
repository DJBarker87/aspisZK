# Session17: proposed Active callback repair (not adopted by lane C)

Lead authorization: LOG D1010; parent11454b6abfe. New A-owned modules only.
Lane C's frozen definitions remain unchanged. No joint witness credit is
claimed before lane C adopts a corrected successor environment/history.

## Before and after

Before, `PV_LIB_SPEC_ReachedNative14.answer` at the actual Adt56 callback
returns `some ⟨pending,w,[]⟩` for every source Store, physical/native frame,
resource selection and OWNER. `PV_LIB_A_ActiveDispatch17.before` preserves
that exact statement and its session16 proof. This is a model defect: the
binary invokes f5's callback and returns.

After, `PV_LIB_A_ActiveDispatch17.resolve` resolves only the actual FnOnce
trait request with f5's empty Adt56 closure and a decoded unary source-reference
tuple. The emitted closure is f207. Its only native operation is f289 on that
Cell reference with replacement true. `boundary` interprets that TLS-only
D727 continuation as a contracted child: it takes the COMPLETE context-bound
f289 reply, applies the named source-store CellReplace289 graph, and delivers
that reply through the original saved return action. It does not return unit
or install an identity source delta. Unsupported/malformed data stays undefined.

`PV_LIB_A_ActiveEnvironment17.step/run` install this boundary only at the
canonical source8162 callback continuation from session16. The existing full
program resolver, allocation resources, context origins and every other native
resolution remain unchanged. `away` is complete Execution equality outside
that dispatch. `PV_LIB_A_ActivePrefix17.prefix` is intended to transport every
retained history index through141, so original85 and A's original141 are used
by name. The final compilation/audit status is recorded below and in HANDOFF;
this document does not by itself claim those draft statements are checked.

## What lane C must adopt

Adopt the checked new A modules, their exact dependency cohort, and the new
`ActiveEnvironment17.step/run` in NEW successor C history/join modules. Keep
`EntryWorld18.Entry`, its complete entry Pre and paired frame, Full.programs,
StoreActionTable.v2 and the context-bound allocation schedule. Use
`ActivePrefix17.prefix` for the retained prefix and `original141` for the suffix
start. Keep f2's FnDef18 forwarding separate from the Adt56 callback. Consume
the stateful CLOSED207/CLOSED289 source/native/source contracts and the named
Cell physical/source graph, including all non-success statuses and complete
world/event/caller frames. Do not edit the retained frozen contracts or claim
that a successful callback's result alone proves the required Cell write.

Lane C decides adoption. Until adoption, all four existing LaneAJoins18
inhabitants and the joint OwnInit witness remain uncredited.
