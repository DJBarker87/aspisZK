import R1Z.PV_RDCD3_CB_OwnedMask
import R1Z.PV_RDCD3_CB_ReverseWrap
import R1Z.PV_RDCD3_CB_MaskHorner
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_OwnedMaskHorner
open Aeneas Aeneas.Std Result PV_RDCD3_ReverseRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
theorem source (coeff : Array Q 27#usize) (p : PV_RDCD3_CB_PreparedTotal.Prepared)
    (fuel : Nat) (e : Usize) (shared : Q) (rank : e.val=fuel) :
    PV_RDCD3_CB_OwnedMask.owned.horner coeff p e shared =
      PV_RDCD3_CB_MaskHorner.finite coeff p fuel e shared := by
  induction fuel generalizing e shared with
  | zero =>
    have zero : e=0#usize := UScalar.eq_of_val_eq rank
    subst e
    rw [PV_RDCD3_CB_OwnedMask.owned.horner]
    simp only [gt_iff_lt,lt_self_iff_false,if_false,PV_RDCD3_CB_MaskHorner.finite]
  | succ fuel ih =>
    have more : e>0#usize := by change e.val>0;omega
    have small : (pred e).val=fuel := by rw [pred_val];omega
    rw [PV_RDCD3_CB_OwnedMask.owned.horner]
    simp only [more,if_true,lift,bind_tc_ok,PV_RDCD3_CB_ReverseWrap.pred_eq e (by omega),PV_RDCD3_CB_MaskHorner.finite,
      PV_RDCD3_CB_MaskHorner.S.add,PV_RDCD3_CB_MaskHorner.S.mul,bind_assoc_eq]
    repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr;intro value hvalue)
    exact ih (pred e) _ small
#print axioms source
end R1Z.PV_RDCD3_CB_OwnedMaskHorner
