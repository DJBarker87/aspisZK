import PV_LIB_SPEC_Native13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ArcPhysical13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ThreadWords12

/-- Resolve Arc360's source-selected allocation to its registered physical
base and check both count planes BEFORE updating them. No physical address,
Store transformer or desired count is an argument. -/
def operands (p : Parameters) (c : Config) (w : OWNER) (args : List Data) :
    Option (Data × Nat × Nat) := do
  let (value,count) ← PV_LIB_SPEC_BoundRuntime.arc (runtime p).carrier c.store w args
  let nonNull ← (runtime p).carrier.field value 0
  let pointer ← (runtime p).carrier.field nonNull 0
  let base ← PV_LIB_SPEC_SparsePacketHandler.physical (runtime p).carrier w pointer
  let physical ← read w base
  if physical.val=count then pure (value,base,count) else none

/-- Mirror exactly the native count increment in OWNER bytes. The source
count increment is still the unchanged lane-A v2 action. All nonsuccess
answers keep their status/events; as in that action, the count write is not
restricted to returned success. Only the literal successful binary JLE test
can replace a success with abort. No overflow-free hypothesis enters a row. -/
def reply (p : Parameters) (c : Config) (w : OWNER) (args : List Data)
    (r : Reply OWNER Event Data) : Option (Reply OWNER Event Data) := do
  let (value,base,count) ← operands p c w args
  let next := (count+1)%2^64
  let changed := write r.world base next
  match r.answer with
  | .returned (.ok _) =>
    if next=0 ∨ 2^63≤next then pure ⟨.fault .abort,changed,r.events⟩
    else pure ⟨.returned (.ok value),changed,r.events⟩
  | _ => pure {r with world := changed}

/-- One symbolic sparse write frame. The count's8 bytes are the only memory
locations this adapter changes, irrespective of the full native outcome. -/
theorem write_away (w : OWNER) (base count address : Nat)
    (outside : address<base ∨ base+8≤address) :
    (write w base count).world.memory address = w.world.memory address := by
  unfold PV_LIB_SPEC_ThreadWords12.write PV_LIB_SPEC_AllocationImages.initialized PV_LIB_SPEC_AllocationImages.overwrite
  dsimp only
  split
  · have hole : wordImage count (address-base) = none := by
      apply if_neg
      omega
    simp only [hole,Option.getD_none]
  · rfl

theorem one_to_two (p : Parameters) (c : Config) (w : OWNER) (args : List Data)
    (value ignored : Data) (base : Nat) (events : List Event)
    (source : operands p c w args = some (value,base,1)) :
    reply p c w args ⟨.returned (.ok ignored),w,events⟩ =
      some ⟨.returned (.ok value),write w base 2,events⟩ := by
  unfold reply
  rw [source]
  rfl

#print axioms operands
#print axioms reply
#print axioms write_away
#print axioms one_to_two
end PV_LIB_SPEC_ArcPhysical13
