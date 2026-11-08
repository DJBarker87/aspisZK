import PV_LIB_SPEC_CellBindings13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_CellPhysical13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- Mirrored scalar Cell<bool>::replace on the finite ACTIVE TLS slot. Its
pre-value is checked in both source and physical memory. Source-store writes
remain the v2 action, including every non-success native answer. -/
def reply (slot : PV_LIB_SPEC_TlsBindings13.Slot) (p : Parameters) (c : Config)
    (w : OWNER) (args : List Data) (r : Reply OWNER Event Data) :
    Option (Reply OWNER Event Data) := do
  let [reference,.boolean b] := args | none
  let address ← (runtime p).carrier.dereference w reference
  if address=slot.source then do
    let old ← PV_LIB_SPEC_TlsBindings13.read slot p c w
    let changed := {r.world with world := {r.world.world with
      memory := fun location => if location=slot.physical then some (if b then 1 else 0)
        else r.world.world.memory location}}
    match r.answer with
    | .returned (.ok _) => pure ⟨.returned (.ok (.boolean old)),changed,r.events⟩
    | _ => pure {r with world := changed}
  else none

/-- Exact byte store has no padding or invented tail bytes. -/
def setByte (slot : PV_LIB_SPEC_TlsBindings13.Slot) (w : OWNER) (b : Bool) : OWNER :=
  {w with world := {w.world with memory := fun location =>
    if location=slot.physical then some (if b then 1 else 0) else w.world.memory location}}

theorem byte (slot : PV_LIB_SPEC_TlsBindings13.Slot) (w : OWNER) (b : Bool) :
    (setByte slot w b).world.memory slot.physical = some (if b then 1 else 0) := if_pos rfl

theorem away (slot : PV_LIB_SPEC_TlsBindings13.Slot) (w : OWNER) (b : Bool) (address : Nat)
    (other : address≠slot.physical) :
    (setByte slot w b).world.memory address = w.world.memory address := if_neg other

#print axioms reply
#print axioms setByte
#print axioms byte
#print axioms away
end PV_LIB_SPEC_CellPhysical13
