# D582 — exact integration boundary

Read OS-BOUNDARY-D582.md and runtime-boundary-D582.json.
Scope: binary-structural (adopted binary), plus OS-model; V370 compiler-cohort.
No new trust field, owner relation, actual-domain witness or native run.

## Unchanged actual-frame target

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

The binders and actual finite prefix domain remain exactly D580/D581's.
`OWNER_actual_prefix` (pv-evhB4, after the lead merges it) is the single named
**owner interpretation dependency**. No substitute owner relation is built.
This is not a claim that an unimplemented actual-prefix domain or the
statement above has now been proved in Lean.

## D582 boundary facts

The reference Linux model supplies permission semantics and the getrandom
payload write contract; the adopted binary supplies requested permissions,
frame offsets and actual syscall register correspondence. The same-prefix
kernel table in OS-BOUNDARY-D582.md uses post-memory to select the complete
returned byte buffer, not independently supplied helper data. The kernel copy
is the OS boundary. Only the requested suffix can receive payload writes;
partial copies/errors, all ordered events, and kernel bookkeeping remain.
The existing `entropy_kernel` covers kernel randomness; T is unchanged.

`KernelMemory.Step` applies at that payload boundary, not across unrelated
signal-handler or other-thread writes. Its OS-model interpretation is a
structural argument. No universal `ValidAnswer`, arbitrary memory function,
empty world, event-silence premise or Lean runtime instance is introduced.

## Pending interpretation and execution

The shared owner relation has not been merged in this checkout. Its exact
exported theorem and module will be named and consumed after the lead's merge.
An actual-prefix source/machine/world carrier and the advancing full native
execution remain absent. No unrelated local law has been written.

The five rtDeployed projections still select OPEN fields. D520/U/D524,
NativeObstruction62/op132, allocator/resource failure fidelity, non-emptiness,
V370/V371/V400 and all L1/L2/L3 obligations are retained. Endpoint/deployment
rows removed NONE; target not yet established. No frozen Rust/program or
soundness source changed. No wallet/key/account/funds action occurred.

## Exact permission coverage remaining independently of OWNER

The requested sole-dependency reduction is not yet justified. For the SAME
four binders and q above (no additional good-stack or future-success filter):

```text
(base : ProverRwFull.ExternalTypes)
(heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
(box : R1Z.PV_RunJoin_WeightInstalled46.Box)
(ops : @ProverRwFull.ExternalFuns
  (R1Z.PV_RunJoin_NativeResidual62.types
    (PV_EVH_NativeRawSelection.rawBase base)))
(q : ActualEntropyEntryPrefix base heap box ops)
  |- forall i : Nat, i < 232 -> mappedRW(q, sp(q)+i)
```

`mappedRW` is the actual-process VMA/protection predicate specified in
OS-BOUNDARY-D582.md. It includes read and write permissions and is stronger
than the target's writable conjunct. No such formal carrier currently exists.
ELF GNU_STACK RW and the OS's RW stack policy prove permissions INSIDE the
stack VMA, not membership of this complete interval before the initializer.
Initial expansion depends on RLIMIT_STACK; later extension is demand-driven.
Prior successful accesses may suffice, but their required all-path bound has
not been established. The arithmetic boundary example in OS-BOUNDARY-D582.md
refutes only the inference from prologue/alignment, not the deployed function.

This is the exact retained portion of FRAME-ENTRY runtime P under l3-1,
not a new premise/T field or a request to pv-evhB4 to assume writable memory.
We cannot honestly label OWNER as the sole remaining dependency of the
UNCHANGED actual_frame_entry until that membership implication is established.
No owner implementation, mapping carrier defined by its desired conclusion,
or conditional wrapper theorem is added to conceal this gap.

Next concrete deliverable: derive actual current stack-region coverage from
entry setup/prior accesses (including reached retries), consume the lead-merged
OWNER interpretation, and connect the per-copy OS model to the same advancing
history. Only then can the full native execution and five projections be
installed. Stopping follows the inherited exact-blocker focus rule; the host
reservation refusals and unspent Lean budget are not the reason for stopping.
