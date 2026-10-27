import LPq_Powers
set_option autoImplicit false
namespace AspisR1.LPq_IndexPorts
open Aeneas Aeneas.Std Result

theorem add (x y : Usize) (h : x.val+y.val<UScalar.size .Usize) :
    x+y=ok (Usize.wrapping_add x y) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) (by scalar_tac))
  have hw := Usize.wrapping_add_val_eq x y
  rw [Nat.mod_eq_of_lt h] at hw
  exact hz.trans (congrArg ok (UScalar.eq_of_val_eq (hv.trans hw.symm)))

theorem mul (x y : Usize) (h : x.val*y.val<UScalar.size .Usize) :
    x*y=ok (Usize.wrapping_mul x y) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.mul_spec (x:=x) (y:=y) (by scalar_tac))
  have hw := Usize.wrapping_mul_val_eq x y
  rw [Nat.mod_eq_of_lt h] at hw
  exact hz.trans (congrArg ok (UScalar.eq_of_val_eq (hv.trans hw.symm)))

#print axioms add
#print axioms mul
end AspisR1.LPq_IndexPorts
