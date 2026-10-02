import AspisR403InterpolateThreeLimb.Funs
import AspisV8R19.R164ProductExecution

/-! Execution of the selected release interpolation helper on six canonical
M31 encodings. The three-term accumulator does not wrap on these inputs.
This does not prove caller canonicality or the complete Poseidon terminal. -/
set_option autoImplicit false
namespace AspisV8R19.R415InterpolationExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase)
open R162WrappedWord (word word_value wrapping_mul_word wrapping_add_word)
noncomputable section

theorem reducer_eq_frozen (x : U64) :
    AspisR403InterpolateThreeLimb.aspis_core.field.M31.reduce_u64 x =
      AspisR156FullFreeze.aspis_core.field.M31.reduce_u64 x := by
  simp only [AspisR403InterpolateThreeLimb.aspis_core.field.M31.reduce_u64,
    AspisR156FullFreeze.aspis_core.field.M31.reduce_u64,
    AspisR403InterpolateThreeLimb.aspis_core.field.reduce_u64,
    AspisR156FullFreeze.aspis_core.field.reduce_u64,
    AspisR403InterpolateThreeLimb.aspis_core.field.P,
    AspisR156FullFreeze.aspis_core.field.P]

theorem from_encode (x : M31Exact) :
    core.convert.num.FromU64U32.from (encodeBase x) = word x.val :=
  R164ProductExecution.widen_encode x

theorem accumulator_bound (w0 w1 w2 c0 c1 c2 : M31Exact) :
    w0.val*c0.val + w1.val*c1.val + w2.val*c2.val < 2^64 := by
  have h0 := PartialProduct.product_bound w0.val c0.val (ZMod.val_lt w0) (ZMod.val_lt c0)
  have h1 := PartialProduct.product_bound w1.val c1.val (ZMod.val_lt w1) (ZMod.val_lt c1)
  have h2 := PartialProduct.product_bound w2.val c2.val (ZMod.val_lt w2) (ZMod.val_lt c2)
  simpa only [Nat.add_zero] using
    PartialDot.fourth_coordinate_bound (w0.val*c0.val) (w1.val*c1.val)
      (w2.val*c2.val) 0 h0 h1 h2 (by decide)

theorem interpolation_raw (w0 w1 w2 c0 c1 c2 : M31Exact) :
    AspisR403InterpolateThreeLimb.aspis_statement.state_only_poseidon.interpolate_three_constant_limb
      (encodeBase w0) (encodeBase w1) (encodeBase w2)
      (encodeBase c0) (encodeBase c1) (encodeBase c2) =
    .ok (encodeBase ((w0.val*c0.val+w1.val*c1.val+w2.val*c2.val : Nat) : M31Exact)) := by
  simp only [AspisR403InterpolateThreeLimb.aspis_statement.state_only_poseidon.interpolate_three_constant_limb,
    from_encode,lift,bind_tc_ok,wrapping_mul_word,wrapping_add_word]
  rw [reducer_eq_frozen]
  exact R164ProductExecution.reduce_word _ (accumulator_bound w0 w1 w2 c0 c1 c2)

theorem interpolation_exact (w0 w1 w2 c0 c1 c2 : M31Exact) :
    AspisR403InterpolateThreeLimb.aspis_statement.state_only_poseidon.interpolate_three_constant_limb
      (encodeBase w0) (encodeBase w1) (encodeBase w2)
      (encodeBase c0) (encodeBase c1) (encodeBase c2) =
    .ok (encodeBase (w0*c0+w1*c1+w2*c2)) := by
  convert interpolation_raw w0 w1 w2 c0 c1 c2 using 1 <;> norm_cast

#print axioms AspisR403InterpolateThreeLimb.aspis_statement.state_only_poseidon.interpolate_three_constant_limb
#print axioms reducer_eq_frozen
#print axioms from_encode
#print axioms accumulator_bound
#print axioms interpolation_raw
#print axioms interpolation_exact
end
end AspisV8R19.R415InterpolationExecution
