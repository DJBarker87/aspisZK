import R1Z.PV_CB_MaskHorner
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_MaskHornerTotal
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
open ProverRwSuccessReverseRange PV_CB_MaskHorner

theorem finite_total (coeff : Coeff) (p : Prepared) (fuel : Nat) (e : Usize) (shared : Q)
    (rank : e.val=fuel) (bound : fuel≤27) : Total (finite coeff p fuel e shared) := by
  induction fuel generalizing e shared with
  | zero => exact ok_total _
  | succ fuel ih =>
    have hi : (pred e).val < (27#usize).val := by rw [pred_val];change e.val-1<27;omega
    simp only [finite]
    apply bind_total (PV_CB_PreparedTotal.mul _ _);intro product
    apply bind_total (ProverRwP6ArrayRead.read coeff (pred e) hi);intro q
    apply bind_total (PV_CB_CurrentTotal.q_add _ _);intro next
    exact ih (pred e) next (by rw [pred_val];omega) (by omega)
theorem loop_total (coeff : Coeff) (p : Prepared) (shared : Q) :
    Total (S.loop (before 26#usize) coeff p shared) := by
  exact (congrArg ProverRwSuccessArithmeticTotal.Total
    (source coeff p 26 26#usize shared rfl)).mpr
    (finite_total coeff p 26 26#usize shared rfl (by decide))
#print axioms finite_total
#print axioms loop_total
end R1Z.PV_CB_MaskHornerTotal
