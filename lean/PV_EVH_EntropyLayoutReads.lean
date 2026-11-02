import PV_EVH_EntropyDeployedLayout
import PV_EVH_EntropyPhysicalReads
set_option autoImplicit false
noncomputable section
namespace PV_EVH_EntropyLayoutReads
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_StackZero (State)
open PV_EVH_EntropyDeployedLayout (original field seed)

/-- Both checked source reads in the adopted frame, with no extent or local
slot-separation input. Physical/native interpretation remains FRAME-CALL. -/
theorem from_delivery [ExternalTypes] (owner sp : Nat)
    (d : PV_EVH_StackEntropyFill.Delivery) (w : State)
    (i : Usize) (hi : i.val < 32) :
    let v := PV_EVH_EntropyPhysicalCopy.copies (original owner sp w)
      (field owner sp w) (seed owner sp w)
      (PV_EVH_EntropyPhysicalCopy.admit_pair (field owner sp w) (seed owner sp w)
        (PV_EVH_StackEntropyFill.post (original owner sp w) d w))
    ∃ x y, Array.index_usize (PV_EVH_EntropyHalves.field d.buffer) i = .ok x ∧
      Array.index_usize (PV_EVH_EntropyHalves.seed d.buffer) i = .ok y ∧
      v.memory ((field owner sp w).address+i.val) = x.val ∧
      v.memory ((seed owner sp w).address+i.val) = y.val := by
  have h := PV_EVH_EntropyDeployedLayout.separation owner sp w
  exact PV_EVH_EntropyPhysicalReads.from_delivery (original owner sp w)
    (field owner sp w) (seed owner sp w) d w rfl rfl rfl h.1 h.2.1 h.2.2 i hi

#print axioms from_delivery
end PV_EVH_EntropyLayoutReads
