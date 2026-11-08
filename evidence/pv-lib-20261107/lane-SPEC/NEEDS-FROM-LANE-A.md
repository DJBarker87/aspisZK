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
