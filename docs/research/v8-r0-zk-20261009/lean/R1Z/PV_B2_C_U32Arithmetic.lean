import Aeneas
set_option autoImplicit false
namespace PV_B2_C_U32Arithmetic
open Aeneas Aeneas.Std Result WP
 theorem add_exact (x y : U32) (h : x.val + y.val ≤ U32.max) :
    x + y = ok (U32.wrapping_add x y) := by
  obtain ⟨z,hz,hv⟩ := spec_imp_exists (U32.add_spec (x := x) (y := y) h)
  have he : z = U32.wrapping_add x y := by
    apply UScalar.eq_of_val_eq
    rw [U32.wrapping_add_val_eq, Nat.mod_eq_of_lt (by
      simpa only [UScalar.size, UScalarTy.numBits, U32.numBits] using
        (show x.val + y.val < 2^U32.numBits from by
          have hp : 0 < 2^U32.numBits := by positivity
          rw [U32.max] at h
          omega))]
    exact hv
  simpa only [he] using hz


#print axioms add_exact
end PV_B2_C_U32Arithmetic
