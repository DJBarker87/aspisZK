# D581 — binary interpretation supplied; actual runtime association still missing

Base `565b5b5715`, branch `codex/pv-evh-20261029`, same worktree.
Read PHYSICAL-D581.md and binary-correspondence-D581.json first.
Evidence class: **binary-structural (adopted binary), plus V370 compiler-cohort**.
The new binary evidence fixes the entry/callback/entropy route, frame sizes,
slot offsets, copy sites and zeroize stores. It replaces the absence of a
binary layout analysis; it does not instantiate the physical execution model.

## Exact first remaining statement (binders unchanged)

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

`ActualEntropyEntryPrefix` must have the actual finite reached-prefix domain
specified in D580 and PHYSICAL-D581.md. It is still NOT implemented. The
proposed source/machine correspondence uses the same entry arguments and
callback capture, actual post-prologue rsp, actual mapped writable addresses,
and same process memory and existing owners. Neither the domain nor state(q)
is defined by requiring this conclusion. No declaration with this name was
added, no arbitrary ghost state was selected, and no proof credit is claimed.

The disassembly establishes the numeric layout and conditional ABI alignment.
It cannot identify the existing abstract live/heap owners with physical memory,
prove their exclusion from the entire reserved frame, or establish every byte's
mapped permissions. At PC 0x1457ef the new original64 initializer has not yet
written; even later accesses do not test all 232 bytes. Those requirements
remain FRAME-ENTRY runtime P; source/machine preservation and ownership
association remain V370/L3 residuals, allowed to be named under l3-1. The exact
consumer chain is recorded in PHYSICAL-D581.md. It remains conditional.

## Kernel association — unchanged, not hidden in the layout

D580's `ValidAnswer` expansion is unchanged. The actual per-reached-call
`KernelMemory.Step` must bind the SAME q's memory before/after, buffer,
world and emitted events at the decoded syscall request. Disassembling
`syscall` proves its register setup, not the kernel's write footprint, mapped
access or preservation of heap/live ownership and world fields. No universal
ValidAnswer over unreached worlds/memories is inferred. A reached-history
consumer needs the actual history and each per-call law. This concrete runtime
instance is still missing; KERNEL-WRITE is runtime P, RAW-ABI is V370.

## Step (2) — checked after lead's merge

The merged pv-evhB source is present on this branch. Its accepted callback and
allocator laws are local, conditional source/world laws. BLOCKER-evhB.md still
requires reached_reserve_header_delivery at the actual deployed owned-vector
instance. Its exact conclusion remains, for the existing runtime/w/v/n binders:

```lean
let e := R1Z.PV_RunJoin_AllocatorWorld63.execute runtime w v n
(runtime.metadata e.world v).address = e.buffer.address ∧
(runtime.metadata e.world v).capacity = e.buffer.capacity
```

This is required on every reached reserve, with the same world and owned vector,
including allocation failure/no-growth/overflow branches, not arbitrary Runtime.
The merge does not supply its concrete instance, physical header invariant or
advancing full salt-loop/thread-resource execution. See the unchanged exact
binder/domain specification in BLOCKER-evhB.md. Do not create another wrapper
assuming those equalities.

All five rtDeployed fields still select named OPEN inputs. The one actual full
advancing run at opsNative, including client/resource/native failures and their
ordered observations, remains missing. Required projections from THAT run:

| Field | Projection |
|---|---|
| native | Same run.events with faithful native terminal conversion |
| fileTrace | PV_RJ4IDB.nativeFiles run.events |
| countTrace | (PV_RJ4IDB.nativeCounts run.events, PV_RJ4IDB.nativeRejections run.events) |
| timeTrace | PV_RJ4IDB.nativeTimes run.events |
| oraclePrefix | PV_RJ4IDB.nativeOracle run.events |

The checker verified the five selectors in the current RuntimeBinding source.
No empty trace, Result-derived count, fixed-world continuation, assumed whole
helper result, or unrelated model witness was installed. D520/U/D524, op132,
NativeObstruction62, non-emptiness and all L1/L2/L3/resource conditions remain.
No endpoint or deployment premise removed; T unchanged. Target not established.

## Validation and stop

N91600 and N91601: admitted with exit0 AND allowed:true in the launch shell;
one scope at a time, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64.
Exact commands, source revisions, exit, wall, RSS, swap and tool hashes are in
receipt-N91600.json and receipt-N91601.json. N91601 adds the full inlined
plan::prove target missing from N91600; it is not an unchanged regression.
The quiet marker was expired at both admissions. No client binary executed.
No Lean source, new axiom, Kani run, full replay or axioms audit. Axioms: N/A
for binary analysis; historical #print axioms remains SUMMARY-BASED.

Stop under the inherited focus rule: the first remaining statement is a missing
actual runtime interpretation, not budget exhaustion or a shipped counterexample.
Native NEXT N91602 (through N91619). Lean NEXT90259, 24 inherited attempts,
then91500–91596; audit91597–91599 untouched. No new local law was added.
Next deliverable: instantiate the actual reached source/machine/owner/world
correspondence with FRAME-ENTRY and same-prefix kernel delivery; discharge
merged reserve header delivery; only then construct full entry and five
projections of one actual run.
