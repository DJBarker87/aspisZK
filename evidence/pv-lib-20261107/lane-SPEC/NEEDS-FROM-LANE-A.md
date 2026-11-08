# Session19: A-S16-2 repair adopted

Focused55783 PASS. C successor history is ActiveAdoption19.history, definitionally
ActivePrefix17.history. A's ActiveEnvironment17.step/run adopted read-only;
EntryWorld18.Entry/Full.programs/v2/resources retained. Exact read-only source
pin: SESSION19_LANEA_INPUT.json. original85/original141 are reused by name.

Newest join target: PV_LIB_SPEC_LaneAJoins19.Joins, now being compiled. This is
the literal LaneAJoins18 milestone/index/order interface on the adopted history.
No values/native/representation/success assumption was added to any field.
Old Joins18 remains the unchanged Before target on the stalling machine; its
unproved later milestones cannot be silently transported through the repair.
Do not rederive C native/Values/stack/ownership proofs. C will derive the
inner8248 setter effect and outer8162 origin consumption on this history.

# Thread-29′ interface, session18 (LOG D1007)

Use NEW `lean/PV_LIB_SPEC_LaneAJoins18.lean`. The old LaneAJoins16 module is
retained, and its fixed Entry14 history is historical evidence only for this
witness. `SESSION18_JOIN_COMPARISON.md` records the exact before/after.

All joins now take `(entry : EntryWorld18.Entry)` and `(activation : Nat)`;
`history entry activation n` is the original v2 ReachedNative14.run with
Full.programs, StoreActionTable.v2, ReachedEnvironment14.parameters and the
native cut derived from that entry's paired native frame. The input is
`EntryWorld18.input entry.world`. The entry includes the COMPLETE OwnInit.Pre,
registered run coordinate, finite stack grant and nonwrapping bounds.

`History18.original85 entry activation` and `LaneAJoins18.original85` supply
the prefix BY NAME. It has five consumed native replies (469/277/278/279/18),
the same world and actual child/caller source cells. `History18.concrete85`
instantiates the physically valid parent1024/scope1016/run1136 entry with
initial stack grant[512,1536), disjoint from all scheduled heap allocations.

The four join targets and Joins have EXACTLY the old source milestones and
index orderings; only the entry/frame parameters changed. Prove them for the
chosen entry (preferably parametrically), exhibit the indices/configurations,
and preserve full stores, worlds, replies, events and suspended frames.
No internal restart, different program table, native desired-success value,
physical-register map, Store transformer or ownership conclusion is supplied.
Native frame activation pairing at actual f361 remains lane C's binding work.

Calls use CLOSED/library contracts by name when they supply the successor.
A missing successor-existence contract must be inventoried before unfolding;
loops use initialized/preserved invariant induction. No successor-machine
projection without proved full-state transport is accepted. Lane C does not
re-derive these joins. All four targets remain OPEN until a named inhabitant
is available. No new endpoint or T premise is introduced.

Read-only lane A atf0baeb4cc44c593682b098b6159f716f840fd47a adopted this
interface and still reports all four joins OPEN (session15 handoff). Its local
F124 resolver and F170Tail15 support are not joins. SESSION18_LANEA_INPUT.json
retains the read-only comparison: all20 source pins unchanged, no join consumed.

---

# Thread-29 interface, session16 (LOG D1005)

The exact elaborated statements are in `lean/PV_LIB_SPEC_LaneAJoins16.lean`.
These are OPEN targets, not assumed endpoint premises or proved joins.
All use the same `Entry14.input`, `ReachedEnvironment14.parameters`,
`Full.programs`, `StoreActionTable.v2`, native cut and continuous resource
history. `LaneAJoins16.original85` supplies original85 by name, for every finite
native stack frame; no fresh internal input may start the suffix.

```lean
def OriginalToF6 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) : Prop :=
  ∃ n6, 85 ≤ n6 ∧ BodyEntry (history stack n6) PV_THR2_F6.live.body

def RangeEntry (q : Execution) : Prop :=
  ∃ (s : Store Data) (a : Nat) (parents : List Frame),
    q.state.current.status = .running (PV_THR2_Source15LoopEnter.after s a parents)

def F6ToRange (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (n6 : Nat) : Prop :=
  ∃ delta, RangeEntry (history stack (n6+delta))

def RangeToF361 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (nr : Nat) : Prop :=
  ∃ delta, BodyEntry (history stack (nr+delta)) PV_THR2_F361.live.body
```

`BodyEntry` quantifies the actual Config, requires its emitted remaining body
and no waiting/completed/unwinding frame. `RangeEntry` requires the actual
`PV_THR2_Source15LoopEnter.after s a parents` configuration. These carry the
actual store and complete native world/events/suspended frames, not an
activation-counter equality across contracted versus expanded calls.

`F361ToInit stack n361` requires four actual original-history indices and
Configs: callback BEFORE allocation at `body.drop 92` (SPEC-C5), registration
at `drop 113`, source Ready at `drop 129`, then InitPoll at readyN+1. They have
one f361 activation and strict ordered indices. It assumes no successful
allocation, payload readback, decoded words, physical-register map or ownership
conclusion. Lane C derives those from the reached states and its bindings.
The complete machine-checkable definition is in the module, including all
quantifiers and index relations. `Joins stack` combines all four targets and
requires original n6 ≤ range nr ≤ f361 n361. An inhabitant must exhibit the
indices/configurations; an implication from a postulated reached target is
insufficient.

Calls must use available CLOSED/library contracts by name under D877; if a
contract cannot furnish the actual successor, inventory the callee unfolded
and the missing existence result. Loops require an initialized and preserved
invariant and induction. A successor-machine result needs a proved transport
preserving states, full replies, failure/pending behavior and event prefixes;
equal acceptance or a final store is insufficient. No successor projection is
adopted by this lane.

Lane C retains native/TLS/physical stack/Values and final joint-witness work.
The old eighteen contracts' fixed runtime versus the context-bound native
assembly still requires full source/machine adequacy; the new operational
prefix is not by itself an inhabitant of `Cut92Composition.Witness`. Lane A's
joins must not package this obligation as a desired-success/native-value or
Store-transformer hypothesis.

Read-only lane A reviewed at 06e2b0233df. Its HANDOFF still states original
entry, v2 transport, full loop/callee preservation and361→14756 are open.
No requested join theorem was available to consume at this checkpoint.
