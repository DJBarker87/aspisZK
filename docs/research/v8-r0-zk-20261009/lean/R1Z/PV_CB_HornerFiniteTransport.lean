import R1Z.PV_CB_HornerFiniteCells
import R1Z.PV_CB_PartialForward
import R1Z.PV_CB_ReachBind
set_option autoImplicit false
namespace R1Z.PV_CB_HornerFiniteTransport
open Aeneas Aeneas.Std Result ProverRwSuccessReverseRange PV_CB_HornerCell

theorem congr (valid : Q → Prop) (left right : Usize → Q → Result Q)
    (preserve : ∀ i value, valid value → PV_CB_PartialForward.Post valid (left i value))
    (agree : ∀ i value, valid value → left i value = right i value)
    (fuel : Nat) (e : Usize) (value : Q) (vv : valid value) :
    PV_CB_HornerFiniteCells.finite left fuel e value =
      PV_CB_HornerFiniteCells.finite right fuel e value := by
  induction fuel generalizing e value with
  | zero => rfl
  | succ fuel ih =>
    simp only [PV_CB_HornerFiniteCells.finite]
    rw [← agree (pred e) value vv]
    apply PV_CB_ReachBind.congr
    intro next hn
    exact ih (pred e) next (preserve (pred e) value vv next hn)
#print axioms congr
end R1Z.PV_CB_HornerFiniteTransport
