import AspisV8R17.GeneratedReducerExpanded

/-! Current generated M31 multiplication and reducer wrapper. The U64 product
fits even for noncanonical U32 inputs; the result is always canonical. -/
namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::mul"]
def aspis_core.field.M31.mul
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← aspis_core.field.reduce_u64 i2
  ok i3
-- END GENERATED

-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::reduce_u64"]
def aspis_core.field.M31.reduce_u64
  (value : Std.U64) : Result aspis_core.field.M31 := do
  let i ← aspis_core.field.reduce_u64 value
  ok i
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedM31Mul
open Aeneas.Std V7Tag73CurrentHelpersOpaque UnsignedReducerOps
open UnsignedCoreSlice GeneratedReducerExpanded

theorem cast_widen_value (x : U32) : (UScalar.cast .U64 x).val = x.val := by
  rw [cast_value]
  apply Nat.mod_eq_of_lt
  have h := x.bv.isLt
  change x.val < 2^32 at h
  change x.val < 2^64
  omega

theorem generated_mul_mod (x y : aspis_core.field.M31) :
    ∃ z : aspis_core.field.M31, aspis_core.field.M31.mul x y = .ok z ∧
      z.val = (x.val*y.val) % RawReducer.P ∧ z.val < RawReducer.P := by
  have hproduct : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val < 2^64 := by
    rw [cast_widen_value, cast_widen_value]
    have h := Nat.mul_lt_mul_of_lt_of_lt x.bv.isLt y.bv.isLt
    exact h
  obtain ⟨product, hp, hv⟩ := mul_success _ _ hproduct
  rw [cast_widen_value, cast_widen_value] at hv
  obtain ⟨z, hz, hzm, hzc⟩ := generated_reducer_mod product
  refine ⟨z, ?_, ?_, hzc⟩
  · simp only [aspis_core.field.M31.mul, lift, bind_tc_ok]
    change (do
      let p ← UScalar.mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)
      let r ← aspis_core.field.reduce_u64 p
      Result.ok r) = Result.ok z
    simp only [hp, bind_tc_ok, hz]
  · simpa only [hv] using hzm

theorem generated_wrapper_mod (x : U64) :
    ∃ z : aspis_core.field.M31, aspis_core.field.M31.reduce_u64 x = .ok z ∧
      z.val = x.val % RawReducer.P ∧ z.val < RawReducer.P := by
  obtain ⟨z, hz, hm, hc⟩ := generated_reducer_mod x
  exact ⟨z, by simp only [aspis_core.field.M31.reduce_u64, hz, bind_tc_ok], hm, hc⟩

#print axioms cast_widen_value
#print axioms generated_mul_mod
#print axioms generated_wrapper_mod
end AspisV8R17.GeneratedM31Mul
