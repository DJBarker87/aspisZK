import R1Z.PV_RunJoin_CircleNeutralWord53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralChecked64_53
open PV_RunJoin_CircleNeutralWord53

theorem add (a b : U64) (h : a.val+b.val < 18446744073709551616) :
    a+b = ok (U64.wrapping_add a b) := by
  apply PV_B2_C_MachineArithmetic.u64_add_exact
  norm_num only [U64.max,U64.numBits,UScalarTy.numBits]
  omega

theorem sub (a b : U64) (h : b.val ≤ a.val) :
    a-b = ok (U64.wrapping_sub a b) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (U64.sub_spec (x := a) (y := b) h)
  have he : z = U64.wrapping_sub a b := by
    apply UScalar.eq_of_val_eq
    rw [sub64 _ _ h]
    exact hv.1
  simpa only [he] using hz

theorem mul (a b : U64) (h : a.val*b.val < 18446744073709551616) :
    a*b = ok (U64.wrapping_mul a b) := by
  obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (U64.mul_spec (x := a) (y := b)
    (by norm_num only [U64.max,U64.numBits,UScalarTy.numBits];omega))
  have he : z = U64.wrapping_mul a b := by
    apply UScalar.eq_of_val_eq
    rw [mul64 _ _ h]
    exact hv
  simpa only [he] using hz

#print axioms add
#print axioms sub
#print axioms mul
end R1Z.PV_RunJoin_CircleNeutralChecked64_53
