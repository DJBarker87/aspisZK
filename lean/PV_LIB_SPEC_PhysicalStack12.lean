import PV_LIB_SPEC_StackReferenceGap12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_PhysicalStack12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen
local instance : DecidableEq Address := Classical.decEq _
open PV_LIB_SPEC_AllocationImages
/-- Finite native frame DATA. `runSource` names the source pointee of &run;
`runPointer` is its physical stack address. This is not a function choosing a
Store/image or a successful-decode premise. Construction of THIS frame from
the actual original-entry call stack remains the source/native obligation. -/
structure Frame where
  activation : Nat
  rsp : Nat
  runSource : Address
  runPointer : Nat

/-- Resolve only this exact initialized source stack place. Other references
retain the existing registered-heap resolution, never a fabricated address.
The native/source pairing is explicit and finite, not hidden in arbitrary C. -/
def physical (native : Frame) (C : Carrier OWNER Data) (c : Config)
    (w : OWNER) (reference : Data) : Option Nat := do
  if c.frame.activation ≠ native.activation then none else do
    let source ← C.dereference w reference
    if source=native.runSource then do
      let _ ← readAddress C c.store source
      pure native.runPointer
    else PV_LIB_SPEC_SparsePacketHandler.physical C w reference

def captureWords (native : Frame) (p : Parameters) (c : Config) (w : OWNER)
    (wrapped : Data) : Option (Nat × Nat) := do
  let closure ← (runtime p).carrier.field wrapped 0
  let reference ← (runtime p).carrier.field closure 0
  let .number k ← (runtime p).carrier.field closure 1 | none
  let pointer ← physical native (runtime p).carrier c w reference
  pure (pointer,k)

def registers (native : Frame) (p : Parameters) (c : Config) (w : OWNER)
    (wrapped packet : Data) : Option PV_LIB_SPEC_CallbackStores.Registers := do
  let packetPointer ← PV_LIB_SPEC_CallbackSource.packetWord (runtime p).carrier w packet
  let (runPointer,k) ← captureWords native p c w wrapped
  pure ⟨native.rsp,packetPointer,runPointer,k⟩

/-- Adopted ELF fc8808eb, no-hooks branch e0550/e0559/e0562/e0565:
cap0 at rsp+0x38; dangling align8 pointer at+0x40; len0/hooksNone0 at+0x48/+0x50.
ALL32 bytes are actually stored, so this is not a padding-zero assumption. -/
def defaultHooks : Image := fun i =>
  if i<8 then word 0 i else if i<16 then word 8 (i-8)
  else if i<24 then word 0 (i-16) else if i<32 then word 0 (i-24) else none

def installDefault (native : Frame) (w : OWNER) : OWNER :=
  initialized (native.rsp+0x38) defaultHooks w

theorem default_mask (i : Nat) : defaultHooks i = none ↔ 32 ≤ i := by
  unfold defaultHooks
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> try { simp only [word,Option.some_ne_none,false_iff]; omega }
  split <;> simp only [word,Option.some_ne_none,false_iff,true_iff] <;> omega

/-- Exact local native/source stack pairing, with initialized source cell and
no invented OWNER registration. The old heap-only codec rejects THIS reference.
This does not claim this native frame was reached from OwnInit entry. -/
def localFrame : Frame := ⟨7,32768,PV_LIB_SPEC_StackReferenceGap12.address,112⟩
def localConfig : Config := ⟨{activation := 7,remaining := []},[],PV_LIB_SPEC_StackReferenceGap12.store⟩

theorem local_resolved :
    physical localFrame PV_LIB_SPEC_StackReferenceGap12.C localConfig
      PV_LIB_SPEC_StackReferenceGap12.before PV_LIB_SPEC_StackReferenceGap12.reference = some 112 := by
  change (if PV_LIB_SPEC_StackReferenceGap12.address = PV_LIB_SPEC_StackReferenceGap12.address
    then some 112 else PV_LIB_SPEC_SparsePacketHandler.physical
      PV_LIB_SPEC_StackReferenceGap12.C PV_LIB_SPEC_StackReferenceGap12.before
      PV_LIB_SPEC_StackReferenceGap12.reference) = some 112
  exact if_pos rfl

theorem local_capture (k : Nat) :
    captureWords localFrame PV_LIB_SPEC_ConcreteEntry.parameters localConfig
      PV_LIB_SPEC_StackReferenceGap12.before
      (PV_THR2_KeyValues.pack PV_LIB_SPEC_NativeKinds.maybeDangling
        [PV_THR2_KeyValues.pack
          (match PV_THR2_F15.node34 with | .leaf (.aggregateMove _ _ kind _) => kind | _ => .null)
          [PV_LIB_SPEC_StackReferenceGap12.reference,.number k]]) = some (112,k) := by
  change (do let pointer ← physical localFrame PV_LIB_SPEC_StackReferenceGap12.C localConfig
              PV_LIB_SPEC_StackReferenceGap12.before PV_LIB_SPEC_StackReferenceGap12.reference
             pure (pointer,k)) = _
  rw [local_resolved]
  rfl

/-- The binary default stores establish the actual stack snapshot copied by
e0614/e0619. No preexisting initialized stack bytes are assumed. -/
theorem default_snapshot (native : Frame) (w : OWNER) (i : Nat) (bound : i<32) :
    ∃ value, defaultHooks i = some value ∧
      (installDefault native w).world.memory (native.rsp+0x38+i) = value := by
  cases h : defaultHooks i with
  | none => have := (default_mask i).mp h; omega
  | some value => exact ⟨value,rfl,stored _ i _ _ value h⟩

theorem copies_default (native : Frame) (w : OWNER) (base packet run k i : Nat)
    (bound : i<32) :
    overwrite base (callback (installDefault native w).world.memory native.rsp packet run k)
      (installDefault native w).world.memory (base+i) =
      (installDefault native w).world.memory (native.rsp+0x38+i) :=
  callback_copy _ _ _ _ _ _ _ bound

theorem stack_ghost (native : Frame) (w : OWNER) :
    (installDefault native w).next = w.next ∧
    (installDefault native w).places = w.places ∧
    (installDefault native w).world.frame = w.world.frame := ghost _ _ _

#print axioms Frame
#print axioms physical
#print axioms captureWords
#print axioms registers
#print axioms defaultHooks
#print axioms installDefault
#print axioms default_mask
#print axioms localFrame
#print axioms localConfig
#print axioms local_resolved
#print axioms local_capture
#print axioms default_snapshot
#print axioms copies_default
#print axioms stack_ghost
end PV_LIB_SPEC_PhysicalStack12
