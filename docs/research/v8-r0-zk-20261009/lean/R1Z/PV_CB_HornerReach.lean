import R1Z.PV_CB_HornerBody
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_HornerReach
open Aeneas Aeneas.Std Result ControlFlow ProverRwSuccessReverseRange
theorem index_bound (e : Usize) (positive : 0<e.val) (upper : e.val≤26) :
    (pred e).val<27 := by
  rw [pred_val]
  omega
theorem body_scalar (coeff : PV_CB_HornerCell.Coeff) (p : PV_CB_HornerCell.Prepared)
    (e : Usize) (shared : PV_CB_HornerCell.Q)
    (positive : 0<e.val) (upper : e.val≤26) :
    ∃ value, PV_CB_MaskHorner.S.body coeff p (before e) shared =
      (do
        let next ← PV_CB_HornerCell.scalar p shared value
        ok (cont (before (pred e),next))) := by
  obtain ⟨value,h⟩ := ProverRwP6ArrayRead.read coeff (pred e) (index_bound e positive upper)
  refine ⟨value,?_⟩
  rw [PV_CB_HornerBody.step coeff p e shared positive,
    PV_CB_HornerCell.read coeff p (pred e) shared value h]
#print axioms index_bound
#print axioms body_scalar
end R1Z.PV_CB_HornerReach
