import Aeneas
set_option autoImplicit false
namespace NDF_CheckedWrapping
open Aeneas Aeneas.Std Result

theorem mul (x y : Usize) (bound : x.val*y.val < UScalar.size .Usize) :
    (x*y : Result Usize) = ok (Usize.wrapping_mul x y) := by
  obtain ⟨z,call,value⟩ := WP.spec_imp_exists (Usize.mul_spec (x:=x) (y:=y) (by scalar_tac))
  rw [call]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [value,Usize.wrapping_mul_val_eq,Nat.mod_eq_of_lt bound]

theorem add (x y : Usize) (bound : x.val+y.val < UScalar.size .Usize) :
    (x+y : Result Usize) = ok (Usize.wrapping_add x y) := by
  obtain ⟨z,call,value⟩ := WP.spec_imp_exists (Usize.add_spec (x:=x) (y:=y) (by scalar_tac))
  rw [call]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [value,Usize.wrapping_add_val_eq,Nat.mod_eq_of_lt bound]

#print axioms mul
#print axioms add
end NDF_CheckedWrapping
