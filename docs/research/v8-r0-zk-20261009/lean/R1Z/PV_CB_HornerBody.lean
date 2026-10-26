import R1Z.PV_CB_HornerCell
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_HornerBody
open Aeneas Aeneas.Std Result ControlFlow ProverRwSuccessReverseRange
abbrev Q := PV_CB_HornerCell.Q
abbrev Coeff := PV_CB_HornerCell.Coeff
abbrev Prepared := PV_CB_HornerCell.Prepared
theorem step (coeff : Coeff) (p : Prepared) (e : Usize) (shared : Q)
    (positive : 0<e.val) :
    PV_CB_MaskHorner.S.body coeff p (before e) shared =
      (do
        let next ← PV_CB_HornerCell.cell coeff p (pred e) shared
        ok (cont (before (pred e),next))) := by
  have h := next_pos e positive
  unfold next at h
  simp only [PV_CB_MaskHorner.S.body,
    PV_CB_MaskSource.state_only_hiding.state_only_selected_mask_value_loop2.body,
    h,bind_tc_ok,PV_CB_HornerCell.cell,PV_CB_MaskHorner.S.mul,
    PV_CB_MaskHorner.S.add,bind_assoc_eq]
  rfl
#print axioms step
end R1Z.PV_CB_HornerBody
