import R1Z.PV_RunJoin_LayoutArithmetic41
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RoundRow73
open Aeneas Aeneas.Std

def row (i : Usize) : U8 := U8.wrapping_add 15#u8 (UScalar.cast .U8 i)

theorem value (i : Usize) (hi : i.val ≤ 10) : (row i).val=15+i.val := by
  have cast : (UScalar.cast .U8 i).val=i.val := by
    rw [UScalar.cast_val_eq]
    change i.val%256=i.val
    exact Nat.mod_eq_of_lt (by omega)
  rw [row,U8.wrapping_add_val_eq,cast]
  change (15+i.val)%256=15+i.val
  exact Nat.mod_eq_of_lt (by omega)

theorem next (i : Usize) (hi : i.val ≤ 10) :
    (U8.wrapping_add (row i) 1#u8).val=16+i.val := by
  rw [U8.wrapping_add_val_eq,value i hi]
  change (15+i.val+1)%256=16+i.val
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem capacity : (13831 : Nat) ≤ Usize.max := by scalar_tac

#print axioms row
#print axioms value
#print axioms next
#print axioms capacity
end R1Z.PV_RunJoin_RoundRow73
