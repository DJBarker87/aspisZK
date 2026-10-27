import R1Z.PV_CB_HornerFiniteCells
import R1Z.PV_CB_ReachBind
set_option autoImplicit false
namespace R1Z.PV_CB_HornerCoefficientPrefix
open Aeneas Aeneas.Std Result ProverRwSuccessReverseRange PV_CB_HornerCell

/-- The reverse recurrence reads only the prefix strictly below its counter.
    Equality includes failures and divergence and needs no canonicality. -/
theorem finite (left right : Coeff) (p : Prepared) (fuel : Nat) (e : Usize) (shared : Q)
    (rank : e.val = fuel)
    (agree : ∀ i : Usize, i.val < e.val → left.index_usize i = right.index_usize i) :
    PV_CB_HornerFiniteCells.finite (cell left p) fuel e shared =
      PV_CB_HornerFiniteCells.finite (cell right p) fuel e shared := by
  induction fuel generalizing e shared with
  | zero => rfl
  | succ fuel ih =>
    have inside : (pred e).val < e.val := by rw [pred_val];omega
    simp only [PV_CB_HornerFiniteCells.finite]
    rw [PV_CB_HornerCell.locality left right p (pred e) shared (agree (pred e) inside)]
    apply PV_CB_ReachBind.congr
    intro next hn
    exact ih (pred e) next (by rw [pred_val];omega)
      (fun i hi => agree i (by rw [pred_val] at hi;omega))
#print axioms finite
end R1Z.PV_CB_HornerCoefficientPrefix
