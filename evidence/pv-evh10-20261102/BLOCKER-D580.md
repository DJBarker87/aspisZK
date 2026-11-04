# D580 — actual entry frame has no supplied interpretation

Base `2c4e247055098415f0005992a0bb49e28b82e082`, branch
`codex/pv-evh-20261029`, same worktree. STOP at requested step (1).
No new local law, Lean source, compiler attempt, native execution or family
installation was made. This is a missing runtime/compiler interpretation,
not budget exhaustion, a host failure, or a counterexample to the shipped code.
`BLOCKER-D579.md` is absent from this checkout; it was not used as evidence.

## First missing lemma: exact binders and domain

The following is a REQUIRED INTERFACE SPECIFICATION, not an elaborated Lean
declaration. The actual-prefix domain and physical interpretation named below
are missing. They must be implemented and bound to the deployed execution;
introducing an arbitrary predicate with this name would not discharge anything.

Fix the adopted binary
`da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0`
and its recorded deployed features/profile from `entry-frame-binding-D572.json`.
Use these binders (Lean names below denote existing types):

```text
(base : ProverRwFull.ExternalTypes)
(heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
(box  : R1Z.PV_RunJoin_WeightInstalled46.Box)
(ops  : @ProverRwFull.ExternalFuns
          (R1Z.PV_RunJoin_NativeResidual62.types
            (PV_EVH_NativeRawSelection.rawBase base)))
```

`ActualEntropyEntryPrefix base heap box ops` must be the FIXED domain of finite
execution prefixes of that adopted proof-account entry, interpreted at
`opsNative (rawBase base) heap box ops`, ending immediately before the
original64 initializer in a reached entropy-loop iteration. Its source route
is `RealR1_client.prove_for_proof_accounts` -> supplied proof-account callback ->
`StateOnlyAttemptSecrets.generate_for_mask_nonce` -> original loop body.
It ranges over the actual entry arguments/captures in the existing extracted
entry signature and the reached retry worlds, after the initial mask guard
and the loop's `retry < limit` guard. It does not require eventual success.
It includes prefixes that subsequently reject, error, fault or exhaust fuel.
It cannot be defined by requiring the conclusion below.

For each prefix `q`, the required source/machine interpretation must extract
`owner(q) : Nat`, `sp(q) : Nat` (actual post-prologue rsp),
`state(q) : PV_EVH_StackZero.State`, and `writable(q) : Nat -> Prop`
(the actual mapped writable process addresses at that prefix). `state(q).memory`
must interpret that SAME process memory, and its live keys and heap must
interpret the SAME existing owners; arbitrary ghost-state choices are forbidden.

The first missing lemma is precisely:

```text
actual_frame_entry
  (base : ProverRwFull.ExternalTypes)
  (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
  (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
  (ops : @ProverRwFull.ExternalFuns
    (R1Z.PV_RunJoin_NativeResidual62.types
      (PV_EVH_NativeRawSelection.rawBase base)))
  (q : ActualEntropyEntryPrefix base heap box ops) :
  let sp := sp(q)
  let w  := state(q)
  sp % 16 = 0 /\ sp + 232 <= 2^64 /\
  (forall i : Nat, i < 232 -> writable(q) (sp+i)) /\
  (forall (b : PV_EVH_Runtime.Block), b ∈ w.frame.runtime.heap ->
    forall i : Nat, i < b.bytes.length ->
      PV_EVH_EntropyDeployedLayout.OutsideFrame sp (b.address+i)) /\
  (forall (old : PV_EVH_StackZero.Slot), old ∈ w.frame.live ->
    forall i : Nat, i < old.initialized ->
      PV_EVH_EntropyDeployedLayout.OutsideFrame sp (old.address+i))
```

The binder types of `b` and `old` are exactly the element types of
`w.frame.runtime.heap` and `w.frame.live`; no separate block/owner carrier is
allowed. The result feeds existing `address_bounds`, `heap_frames`,
`live_frames` and `original_admission` at `owner(q), sp(q), state(q)`.
The actual mask input, caller Result destination, ABI extent/padding and their
aliasing interpretation remain additional FRAME-ENTRY requirements, not
consequences of this minimal first missing lemma. No allocator-fidelity work
from the parallel slice was imported.

## Why the existing entry cannot supply it

`PV_EVH_NativeOperatorProver.entry_OPEN` is a composition with open callees;
its `entry_fixed` proves conditional `FinishedView` Result transport.
`PV_EVH_Prefix.P A = PV_EVH_World.World -> Prefix A`. That World contains
entropy/file/oracle/count fields, but no rsp, physical memory, mapped-address
permissions or machine reachability relation. `OperatorFrames.Frames` supplies
invoke/drop computations, not a physical stack-frame interpretation.

`StackZero.State` has an arbitrary total `Nat -> Nat` memory and ghost owners.
`EntropyDeployedLayout` proves numeric offset separation and admission FROM
outside-frame hypotheses. Its `address_bounds` explicitly requires
`sp+232 <= 2^64`. Arbitrary Nat bases include `sp = 2^64`, so dropping the
actual-prefix domain would make even that conclusion false. This observation
concerns the model domain; it is not a shipped-source counterexample.

The adopted `sub rsp,232` and relative offsets establish a layout under
compiler preservation. They do not establish mapped writable memory or
disjointness of actual owners. No unoccupied address or safe entry state can
be manufactured to fill this gap. FRAME-CALL/RAW-ABI remain V370 compiler-cohort
P; FRAME-ENTRY remains runtime P. None is a new T field.

## Dependent kernel instance is also absent

The existing `PV_EVH_KernelMemory.ValidAnswer` obligation consumed by
`PV_EVH_RawMemoryReification.driver_memory` has the following exact expansion:

```text
-- Under the ExternalTypes instance types (rawBase base):
(kernel : Nat -> Nat -> Aeneas.Std.Array Aeneas.Std.U8 64#usize ->
  PV_EVH_World.World -> PV_EVH_LinuxRawControl.Reply)
(memory : PV_EVH_RawMemoryHistory.MemoryAnswer)
(address : Nat)

forall offset : Nat, offset <= 64 ->
forall (a : Aeneas.Std.Array Aeneas.Std.U8 64#usize)
       (v : PV_EVH_World.World) (m : PV_EVH_KernelMemory.Memory),
  PV_EVH_KernelMemory.Backed address a m ->
  PV_EVH_KernelMemory.Step address offset m
    (memory (address+offset) (64-offset) a v m)
    (kernel (address+offset) (64-offset) a v).buffer
```

This is a premise, not a Linux instance. The actual kernel and memory-answer
functions, and their association with the SAME prefix's world, memory and
events, have not been selected. The universal quantifiers above also include
unreached buffers/worlds/memories. Do not claim that a reached-only kernel law
proves this stronger universal premise. A reached-only consumer can instead
use `RawMemoryHistory.threaded`'s per-call `hv` after supplying the actual
history and physical interpretation; none has been supplied here.

`ValidAnswer` constrains the buffer's physical backing and suffix footprint.
It does not constrain `Reply.world`, ownership, allocator/handles, or native
events. `LinuxRawControl.driver` preserving fields by construction is not
evidence that an actual Linux syscall preserves the corresponding machine
state. The full KERNEL-WRITE/world/ownership association remains runtime P,
with ABI/compiler preservation separately retained under V370.

## Step (2), validation and restart

All five requested `rtDeployed` fields still select their corresponding
`OpenDeploymentInputs` fields: `native_OPEN`, `fileTrace_OPEN`,
`countTrace_OPEN`, `timeTrace_OPEN`, `oraclePrefix_OPEN`. No single actual
complete advancing `worldRun` at opsNative is supplied by the inspected entry.
Generic projections cannot establish its provenance. Installation therefore
remains blocked; no empty events or Result-derived trace was substituted.
D520/U/D524, NativeObstruction62/op132, non-emptiness, and all retained L1/L2/L3
and runtime/compiler/deployment obligations remain. T is unchanged.
Endpoint/deployment rows removed: NONE. Target not yet established.

Read-only focused checks on this base: `frame_binding.py --check`,
`entry_frame_binding.py --check`, `raw_frame.py --check`: all exit 0. These
check source/layout bindings and explicitly retain the gaps above. No full
regression, host scope, axioms audit or release replay was run. No new theorem
or proof credit is claimed; historical axiom outputs remain SUMMARY-BASED.

Next ID remains **90259**, with **24 attempts** remaining in the inherited
allowance, then the NEW **91500-91596** block; audits **91597-91599** reserved.
No ID was submitted or consumed. Existing audit reserves remain untouched.
The exact next deliverable is the actual-prefix physical interpretation and
`actual_frame_entry` above, followed by the same-prefix kernel instance and
complete advancing entry producer. Do not resume unrelated local-law work.
