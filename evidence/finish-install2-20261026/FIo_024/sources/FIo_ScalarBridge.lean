import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.FIo_ScalarBridge

theorem add {ty : UScalarTy} (x y : UScalar ty)
    (h : x.val+y.val < UScalar.size ty) :
    x+y=ok (UScalar.wrapping_add x y) := by
  obtain ⟨z,hz,hval⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=x) (y:=y) (by scalar_tac))
  have he : z=UScalar.wrapping_add x y := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.wrapping_add_val_eq,Nat.mod_eq_of_lt h]
    exact hval
  simpa only [he] using hz

#print axioms add
end AspisR1.FIo_ScalarBridge
