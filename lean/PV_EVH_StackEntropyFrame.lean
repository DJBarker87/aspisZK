import PV_EVH_StackEntropyCoherence
set_option autoImplicit false
noncomputable section
namespace PV_EVH_StackEntropyFrame
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_StackZero (Slot State)
open PV_EVH_StackAdmission (enter LiveSeparate Outside write_outside)
variable [ExternalTypes]

/-- Initializer, arbitrary partial fill and deployed cleanup touch only the
original slot. This protects bytes of every pre-existing LIVE stack owner;
retired slots may reuse addresses and are deliberately not asserted unchanged. -/
theorem cleanup_live_memory (slot old : Slot) (d : PV_EVH_StackEntropyFill.Delivery)
    (bytes : PV_RJ4IDB.Bytes) (w : State)
    (hs : LiveSeparate slot w) (ho : old ∈ w.frame.live)
    (i : Nat) (hi : i < old.initialized) :
    (PV_EVH_StackZero.drop slot (PV_EVH_StackEntropyFill.post slot d
      (enter slot bytes w))).memory (old.address+i) = w.memory (old.address+i) := by
  have hx : Outside slot (old.address+i) := hs old ho i hi
  rw [PV_EVH_StackZero.outside_preserved slot _ (old.address+i) hx]
  change (PV_EVH_StackAdmission.write slot (PV_EVH_StackEntropyFill.encode d.buffer)
    (enter slot bytes w)).memory (old.address+i) = _
  rw [write_outside slot _ _ _ hx]
  exact PV_EVH_StackAdmission.enter_live slot old bytes w hs ho i hi

#print axioms cleanup_live_memory
end PV_EVH_StackEntropyFrame
