import R1Z.PV_CB_MaskLinearsFinite
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_MaskLinearsTotal
open Aeneas Aeneas.Std Result ProverRwSuccessArithmeticTotal
open ProverRwSuccessReverseRange PV_CB_MaskLinearsFinite

theorem finite_total (point : Points) (fuel : Nat) (e : Usize) (suffix weighted : Q)
    (size : e.val=fuel) (bound : fuel≤10) :
    Total (finite point fuel e suffix weighted) := by
  induction fuel generalizing e suffix weighted with
  | zero => exact ok_total _
  | succ fuel ih =>
    have hi : (pred e).val < (10#usize).val := by rw [pred_val];change e.val-1<10;omega
    simp only [finite]
    apply bind_total (ProverRwP6ArrayRead.read point (pred e) hi);intro q
    apply bind_total (PV_CB_CurrentTotal.q_add _ _);intro s
    apply bind_total (show Total (if pred e != 0#usize then S.add weighted s else .ok weighted) from by
      split
      · exact PV_CB_CurrentTotal.q_add _ _
      · exact ok_total _)
    intro w
    exact ih (pred e) s w (by rw [pred_val];omega) (by omega)
theorem loop_total (point : Points) (suffix weighted : Q) :
    Total (S.loop (before 10#usize) point suffix weighted) := by
  rw [source point 10 10#usize suffix weighted rfl]
  exact finite_total point 10 10#usize suffix weighted rfl (by decide)
theorem linears_total (point : Points) :
    Total (PV_CB_MaskSource.state_only_hiding.selected_mask_linears point) := by
  unfold PV_CB_MaskSource.state_only_hiding.selected_mask_linears
  simp only [core.iter.traits.iterator.Iterator.rev.trait_default,bind_tc_ok]
  apply bind_total (loop_total point _ _)
  intro pair
  rcases pair with ⟨suffix,weighted⟩
  apply bind_total (PV_CB_CurrentTotal.q_scale _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_scale _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_add _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_scale _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_scale _ _);intro _
  apply bind_total (PV_CB_CurrentTotal.q_add _ _);intro _
  exact ok_total _
#print axioms finite_total
#print axioms loop_total
#print axioms linears_total
end R1Z.PV_CB_MaskLinearsTotal
