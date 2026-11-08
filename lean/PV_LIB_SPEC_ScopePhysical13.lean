import PV_LIB_SPEC_ArcPhysical13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ScopePhysical13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ThreadWords12

/-- The actual reference to ArcInner.data ends in source field2. Strip only
that field to select its registered allocation; ScopeData's native counter
is at allocation+24 (fa0c6,17bdf0). A reference to an arbitrary local or an
unregistered ancestor is explicitly unsupported. -/
def operands (p : Parameters) (c : Config) (w : OWNER) (args : List Data) : Option (Nat × Nat) := do
  let [reference] := args | none
  let address ← (runtime p).carrier.dereference w reference
  let parent := {address with fields := address.fields.dropLast}
  if address.fields ≠ parent.fields ++ [2] then none else do
    let (_,header) ← receiver w ⟨parent.activation,parent.localIndex :: parent.fields⟩
    if header.shape.width≠40 then none else do
      let .number count ← readAddress (runtime p).carrier c.store
        {address with fields := address.fields ++ [0,0,0]} | none
      let physical ← read w (header.pointer+24)
      if physical.val=count then pure (header.pointer+24,count) else none

/-- Native457's normal increment mirrored in bytes. Overflow compensation
is the same named source arithmetic as lane-A v2: its final value is old.
The full overflow's panic/event semantics still need their native binding;
this function certifies only the byte projection, never a universal row. -/
def reply (p : Parameters) (c : Config) (w : OWNER) (args : List Data)
    (r : Reply OWNER Event Data) : Option (Reply OWNER Event Data) := do
  let (base,count) ← operands p c w args
  let next := if count > 2^64/2-1 then count else (count+1)%2^64
  pure {r with world := write r.world base next}

theorem one_to_two (p : Parameters) (c : Config) (w : OWNER) (args : List Data)
    (r : Reply OWNER Event Data) (base : Nat)
    (source : operands p c w args = some (base,1)) :
    reply p c w args r = some {r with world := write r.world base 2} := by
  unfold reply
  rw [source]
  rfl

#print axioms operands
#print axioms reply
#print axioms one_to_two
end PV_LIB_SPEC_ScopePhysical13
