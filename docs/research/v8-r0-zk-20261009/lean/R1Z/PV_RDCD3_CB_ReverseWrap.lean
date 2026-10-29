import R1Z.PV_RDCD3_CB_ForwardRange
set_option autoImplicit false
namespace R1Z.PV_RDCD3_CB_ReverseWrap
open Aeneas Aeneas.Std Result PV_RDCD3_ReverseRange
theorem pred_eq (e : Usize) (positive : 0<e.val) :
    Usize.wrapping_sub e 1#usize = pred e := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_sub_val_eq,pred_val]
  have bound : e.val<UScalar.size .Usize := by rw [UScalar.size];exact e.hBounds
  change (e.val+(UScalar.size .Usize-1))%UScalar.size .Usize=e.val-1
  rw [show e.val+(UScalar.size .Usize-1)=(e.val-1)+UScalar.size .Usize from by omega,
    Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
#print axioms pred_eq
end R1Z.PV_RDCD3_CB_ReverseWrap
