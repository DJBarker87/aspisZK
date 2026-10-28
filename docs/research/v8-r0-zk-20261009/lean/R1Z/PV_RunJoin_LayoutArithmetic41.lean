import R1Z.PV_RunJoin_CompactStep39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LayoutArithmetic41
open Aeneas Aeneas.Std

theorem mul (a b c : Usize) (value : a.val*b.val=c.val) :
    Usize.wrapping_mul a b=c := by
  apply UScalar.eq_of_val_eq
  rw [Usize.wrapping_mul_val_eq]
  have bound : a.val*b.val≤Usize.max := by rw [value];scalar_tac
  have size := Usize.max_succ_eq_pow
  rw [UScalar.size_def,UScalarTy.Usize_numBits_eq]
  rw [Nat.mod_eq_of_lt (by omega)]
  exact value

theorem add (a b c : Usize) (value : a.val+b.val=c.val) :
    Usize.wrapping_add a b=c := by
  apply UScalar.eq_of_val_eq
  rw [PV_RunJoin_CompactStep39.offset a b (by rw [value];scalar_tac)]
  exact value
#print axioms mul
#print axioms add
end R1Z.PV_RunJoin_LayoutArithmetic41
