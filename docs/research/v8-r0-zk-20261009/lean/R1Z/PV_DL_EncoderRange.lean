import Aeneas
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_EncoderRange
set_option autoImplicit false
def advance (j : Usize) : Usize := Usize.wrapping_add j 1#usize

theorem advance_val (j : Usize) (bound : j.val<512) :
    (advance j).val=j.val+1 := by
  rw [advance,Usize.wrapping_add_val_eq]
  change (j.val+1)%UScalar.size .Usize=j.val+1
  apply Nat.mod_eq_of_lt
  have big := (512#usize).hSize
  change 512<UScalar.size .Usize at big
  omega

theorem even (j : Usize) (inside : j.val<512) :
    (Usize.wrapping_mul 2#usize j).val=2*j.val := by
  rw [Usize.wrapping_mul_val_eq]
  change (2*j.val)%UScalar.size .Usize=2*j.val
  apply Nat.mod_eq_of_lt
  have big := (1024#usize).hSize
  change 1024<UScalar.size .Usize at big
  omega

theorem odd (j : Usize) (inside : j.val<512) :
    (Usize.wrapping_add (Usize.wrapping_mul 2#usize j) 1#usize).val=2*j.val+1 := by
  rw [Usize.wrapping_add_val_eq,even j inside]
  change (2*j.val+1)%UScalar.size .Usize=2*j.val+1
  apply Nat.mod_eq_of_lt
  have big := (1024#usize).hSize
  change 1024<UScalar.size .Usize at big
  omega

#print axioms advance
#print axioms advance_val
#print axioms even
#print axioms odd
end R1Z.PV_DL_EncoderRange
