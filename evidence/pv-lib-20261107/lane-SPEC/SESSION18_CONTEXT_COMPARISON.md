# SPEC-C14 successor statements — thread-29′ / D1007

The BEFORE statements remain unchanged in ThreadSpecifications,
F316Callback, OwnInitCut92Contract and Cut92Composition. Each new row module
exports its actual compiled BEFORE statement by name and a literal Pre equality.
New statements are specifications, not proofs of universal row adequacy.

## Common before/after

BEFORE: the machine is D984.Machine, fixed handler `(runtime p).native`,
fixed resources `p.resources`, full table as a parameter. At the original84
poll this fixed native returns Ok(null), while the source/TLS adapter returns
Ok(false): FixedNativeGap17.no_reply_identity is the checked incompatibility.

AFTER: ContextMachine18.Machine runs over ResourceHistory.Execution, including
State, issued origins and consumed origins. Its MachineSpec equates its entire
next transition to ReachedNative14.step cut p, which uses the retained
StoreActionTable.v2, Full.programs and actual source/configuration native
adapter, and binds resources at the actual origin/occurrence/operands/world.
There is no native/store-success premise, table delta or desired-write field.
The table is now the explicitly adopted v2 rather than an existential candidate.
Table adequacy is still a joint-witness obligation, not silently discharged.

Pre is exactly the old row Pre. Initial issued/consumed lists are additional
execution DATA, universally quantified, not restrictions or success assumptions.
Post uses the same complete reference behavior on this context machine, the
same completion/delivery/InitPoll frontier, and the exact old source frame
predicate. Pending is tested on the actual transition. All failure/pending/
divergence arms and event prefixes remain. Abort/panic observation is only the
event prefix; other observations retain the complete Execution, including both
origin lists. This is a stronger full-state record, not an output projection.
Implementations therefore return Execution traces rather than bare State traces.

The new contracts do not assert equivalence to the incompatible old runtime.
No row proof, ledger, endpoint premise, T field or frozen source is changed.

## f361 provider association

BEFORE F361.MachineSpec conjoins the fixed Frozen.MachineSpec with the provider's
fixed MachineSpec (carrier, control, programs, native, resources, encode, table).
AFTER ContextF36118.MachineSpec retains exact provider carrier/control/programs/
encoder association; the fixed native/resources identifications are replaced
by the complete context transition specified above. The old Input's historical
native/resources slots are not executed by the successor. The full provider
Pre and source Frame/Numbered predicates remain exact. Universal correctness
and provider/source adequacy are still required proofs, not adopted assumptions.

## Per-row record

The row modules and their compiled Before/Pre/Post/Contract declarations are
listed in SESSION18_STATUS.json once validated. Ordinary rows retain
ThreadRow.Frame; f361 retains its provider Frame and Numbered; f316 retains
F316Callback.Frame and intrinsic entry; f318 retains Delivered; f0 retains its
original/call split and RootFrame; OwnInit retains the corrected cut92 milestone
and same-history source ownership conclusion, with per-origin resources.
