import R1Z.PV_RDCD3_CB_OwnedMask
import R1Z.PV_RDCD3_CB_ReverseWrap
import R1Z.PV_RDCD3_CB_MaskLinearsFinite
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD3_CB_OwnedMaskLinears
open Aeneas Aeneas.Std Result PV_RDCD3_ReverseRange
abbrev Q := ProverRwFull.aspis_core.field.QM31
 theorem source (point : Array Q 10#usize) (fuel : Nat) (e : Usize) (suffix weighted : Q)
    (rank : e.val=fuel) :
    PV_RDCD3_CB_OwnedMask.owned.linears_fold point e suffix weighted =
      PV_RDCD3_CB_MaskLinearsFinite.finite point fuel e suffix weighted := by
  induction fuel generalizing e suffix weighted with
  | zero =>
    have zero : e=0#usize := UScalar.eq_of_val_eq rank
    subst e
    rw [PV_RDCD3_CB_OwnedMask.owned.linears_fold]
    simp only [gt_iff_lt,lt_self_iff_false,if_false,PV_RDCD3_CB_MaskLinearsFinite.finite]
  | succ fuel ih =>
    have more : e>0#usize := by change e.val>0;omega
    have small : (pred e).val=fuel := by rw [pred_val];omega
    rw [PV_RDCD3_CB_OwnedMask.owned.linears_fold]
    simp only [more,if_true,lift,bind_tc_ok,PV_RDCD3_CB_ReverseWrap.pred_eq e (by omega),PV_RDCD3_CB_MaskLinearsFinite.finite,
      PV_RDCD3_CB_MaskLinearsFinite.S.add,bind_assoc_eq]
    repeat' (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr;intro value hvalue)
    exact ih (pred e) _ _ small
#print axioms source
end R1Z.PV_RDCD3_CB_OwnedMaskLinears
