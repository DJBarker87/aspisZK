# Continuation adoption scope

No shipped file changes. The generator pins frozen candidate.rs and multiproof.rs;
--check validates all cut bodies and output bytes. The binary_level cut is one
complete outer iteration of verify_in_place with Arity::Two. The leaf iteration
is the complete key-read/cursor/hash/duplicate/write body of batch_tree.

The first direct whole-level BMC timed out while unrolling, with no completed
solver result. It is not evidence. Its 512-byte diagnostic bound also does not
cover every frozen slot. The replacement attempts a full-state source_row contract followed by a
composed level gate, both using the entire
5504-byte maximum slot bound (172*32). The leaf-hash wrapper has no external
mutable state: its exact digest, event byte, call count and input lengths are
part of the verified return contract. Source_row is intended to return every scratch byte, cursor and oracle effect.
Its currently UNVERIFIED contract does not weaken these
postconditions to a single coordinate.

Each final step harness uses universally arbitrary scratch and oracle-event
observation coordinates. The level answer tape has independent answers by
call ordinal. Equality of all ordinals/bytes plus exact call count/component
lengths identifies the ordered local oracle transcript. Rejection retains
partial scratch and skips the remaining work. These are P6 certificates,
not kernel conversion of Kani output into Lean theorems.

The generated adoption_level.rs factors the exact binary_group into source_row,
retaining the source i<n loop, updates and n=w. Its control/template extraction
is a trust boundary alongside the frozen-cut ledger. The induction in
MultiproofConeLevelIteration proves exact full-Result equality between structural
iteration and the actual extracted MultiproofConeRef.reference.levels through
height 18. adopt_eighteen explicitly requires the one-level source equation;
it is not a claimed proof of that P6 boundary inside Lean.

The selected opening is supplied to the leaf step together with its key and
relative-position projection. Mapping that borrowed slice to the stored proof
and linking batch_keys/sort/count/padding/final root to the reached caller remain
separate. Caller lowering waits on S2. No AcceptedRunJoin is constructed here.

Final disposition: the direct whole-level attempt and both full-state row
contract attempts timed out with zero completed solver results. Inlining the
byte reader did not remove the propositional-reduction bottleneck. The composed
level gate was NOT RUN because its verified-callee prerequisite is missing.
Do not use source_row as a verified stub in a claimed certificate. The leaf
contract and leaf-batch step both passed; the height induction is conditional
on the precise one-level certificate and preservation premises. This packet
stops at the requested resource blocker, without a cap increase or a complete
source-cone claim. A next attempt should isolate the sibling/short/occupied
full-state frames and symbolic slice window before composing a level.

## Continuation 3: separated node windows

The replacement does not rerun any failed level/row gate. `adoption_node.rs`
uses the generated, unmodified `binary_group` body on an arbitrary window of
0..32 symbolic bytes, with cursor zero. Occupied, sibling and short cases are
separate harnesses. Scratch, n/i/w, hash reply and event-byte coordinate remain
arbitrary. A separately verified `hash_parts` observer checks 1/32/32 component
lengths, digest, one-call count and the selected byte; its effects are returned,
then accounted for by local Cells. Only this checked hash observer is stubbed.
No row or level is stubbed. `same_scratch` checks arbitrary independent idx and
val coordinates plus n/at. `scratch_ext` states the kernel extensionality rule.

`node_digest_equality` separately checks the exact copied `root_matches` body.
The generator only exposes its visibility. `node_domain_preservation` checks
one row's cursor advance/write bound and success/rejection call count, without
an equality postcondition. These six results are in cone3-hash-1 (one) and
cone3-nodes-1 (five). Their receipt snapshots pin all executable inputs.

The physical buffer is **not** silently replaced by this window. The kernel
`MultiproofConeNodeWindow.physical_read` proves the checked range/read32
composition reads the exact original 32-byte window on arbitrary slices;
`short_iff` covers the missing-sibling test. The production `.get`/relative
cursor rebase and source-loop factoring must still be connected through the
P6/library lowering boundary. No gate here checks all 5504 physical bytes in
one BMC invocation, and no physical-slot source equation is claimed from the
window harness alone.

`binary_step_progress` checks the actual extracted body. `rows_eq_extracted`
proves finite node iteration equals the extracted partial-fixpoint level;
`level_preserve` derives the nonempty frontier domain after successful levels.
`NodeAdoption.eighteen_eq` composes a *one-node* equation through the level and
height 18. It removes the old complete-level equation and preservation premises,
retaining the explicit local node equation and total oracle. It compares full
Results/scratch; it does not encode a source oracle-log carrier or identify the
frozen list model.

The complete-cone consumer is now `OraclePortFrozen2Join.AcceptedRunJoin` via
`OraclePortFrozen2Cones`; the slot program itself remains `verifySlot_frozen`
in batch0 before checkpoint and batch1 after resume. The missing obligations
are physical source-window adoption; the sorted live-prefix/safe-overwrite and
scratch-suffix representation; ordered list-model row simulation; initial
keys/openings, leaf/count/padding/root adapters; and both three-slot batches.
Caller lowering waits on S2. No whole-cone completion follows from the new
local gates or conditional height theorem.

## Continuation 4: physical cursor adoption

`physical_node.rs` now compares the exact generated binary_group on the full
physical slot against the same body on its separated window, with relative
cursor zero. The physical array has 5504 arbitrary bytes; physical length,
cursor, n/i/w, scratch, reply and event/array observation coordinates are
symbolic. Occupied, sufficient-sibling and short-sibling roots are separate.
The window is borrowed directly from the physical slice, never filled with
replacement bytes. Both sides use actual `.get` and cursor updates. There is
no read32, row or level stub; the sole stub is the unchanged verified hash
observer. Rebase checks all indices/digest bytes extensionally, exact cursor
translation, success/rejection, i/w, hash count and every address coordinate.

All three roots passed in `cone4-physical-1`. This closes the bounded P6
physical-to-window cut that was missing in continuation 3. The independent
kernel `physical_read`/`short_iff` facts and prior window-to-owned-reference
gates are retained. Kani certificates remain the explicit P6 source/library
boundary; they are not automatically imported into Lean as proof terms.
Whole-loop source factoring, ordered list-model simulation and both batch
callers still require their own composition. No complete source ConeJoin or
AcceptedRunJoin is constructed by the physical cut.
