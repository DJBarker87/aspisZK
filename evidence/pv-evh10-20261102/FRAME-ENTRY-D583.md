# D583 — branch-valued actual frame target

Required interface specification only. The actual carrier and shared OWNER
are not implemented in this checkout; names below are semantic interface
names, not invented Lean declarations. No type-check/proof credit is claimed.

```text
actual_frame_entry
  (base : ProverRwFull.ExternalTypes)
  (heap : R1Z.PV_RunJoin_WeightInstalled46.Heap)
  (box : R1Z.PV_RunJoin_WeightInstalled46.Box)
  (ops : @ProverRwFull.ExternalFuns
    (R1Z.PV_RunJoin_NativeResidual62.types
      (PV_EVH_NativeRawSelection.rawBase base)))
  (OWNER : OWNER_actual_prefix base heap box ops)
  (q : ActualEntropyEntryPrefix base heap box ops) :
  match stackAnswer(q) with
  | granted =>
    let sp := sp(q)
    let w := state(q)
    sp % 16 = 0 /\ sp + 232 <= 2^64 /\
    (forall i : Nat, i < 232 -> writable(q) (sp+i)) /\
    (forall (b : PV_EVH_Runtime.Block), b ∈ w.frame.runtime.heap ->
      forall i : Nat, i < b.bytes.length ->
        PV_EVH_EntropyDeployedLayout.OutsideFrame sp (b.address+i)) /\
    (forall (old : PV_EVH_StackZero.Slot), old ∈ w.frame.live ->
      forall i : Nat, i < old.initialized ->
        PV_EVH_EntropyDeployedLayout.OutsideFrame sp (old.address+i))
  | exhausted =>
    q's same world run retains its ordered stack-fault/abort prefix,
    and does not continue through secret initialization as successful entry
```

The resource case split is internal, not an additional hypothesis. The grant
conjuncts reproduce the old frame statement. Pending resource outcomes are
resolved in the advancing continuation; exhaustion can occur on the first
initializer access. The actual domain still contains the finite prefixes
that subsequently fail: no `stackGranted q` binder or domain filter is added.
Use actual post-answer mapping when a demand growth changes the world;
never retroactively assert its residence in the pre-answer VMA. This is the
explicit D583 change to D582's pre-answer-writability interpretation.

Structural derivation: six pushes/sub232 preserve the SysV alignment;
nonwrapping granted RW interval supplies bounds and writability; OWNER's
interpretation of existing runtime heap and live slots, lifetimes and active
machine frames supplies the last two conjuncts. OutsideFrame still uses all
232 bytes. OWNER is consumed from the shared slice only after lead merge;
this document does not define an alternative relation. Exact exported Lean
name/signature must be substituted after that merge, never guessed.

The granted result then feeds EntropyDeployedLayout.address_bounds,
heap_frames, live_frames and original_admission at the SAME sp/owner/state.
KernelMemory.Step applies separately at each same-prefix Linux payload copy
as specified in OS-BOUNDARY-D582; it does not grant stack resources or bind
an unrelated memory. Returned mask and Result use corrected sp+304 and
sp+352 offsets from STACK-RESOURCE-D583. No whole-client L3 closure follows.
