import ExtractedMaskReducer
import PoseidonRemainingConstantsExact
import AspisV8R15.ExactTowerBase

/-! The exact scalar interpolation source uses three checked widening
products and two checked additions. Their bounds follow from canonical M31
inputs, and the existing unrestricted U64 reducer supplies the result. -/
set_option autoImplicit false
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result
/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolate_three_constant_limb]:
    Source: 'src/statement/state_only_poseidon.rs', lines 420:0-433:1 -/
def state_only_poseidon.interpolate_three_constant_limb
  (weight0 : Std.U32) (weight1 : Std.U32) (weight2 : Std.U32)
  (constant0 : Std.U32) (constant1 : Std.U32) (constant2 : Std.U32) :
  Result field.M31
  := do
  let i ← lift (core.convert.num.FromU64U32.from weight0)
  let i1 ← lift (core.convert.num.FromU64U32.from constant0)
  let i2 ← i * i1
  let i3 ← lift (core.convert.num.FromU64U32.from weight1)
  let i4 ← lift (core.convert.num.FromU64U32.from constant1)
  let i5 ← i3 * i4
  let i6 ← i2 + i5
  let i7 ← lift (core.convert.num.FromU64U32.from weight2)
  let i8 ← lift (core.convert.num.FromU64U32.from constant2)
  let i9 ← i7 * i8
  let i10 ← i6 + i9
  field.M31.reduce_u64 i10


end AspisR1SelectedMaskProbe
namespace AspisR1.PoseidonThreeConstantLimb
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskReducerOps AspisV8R17.RawReducer

abbrev wide (x : U32) : U64 := core.convert.num.FromU64U32.from x

theorem wide_value (x : U32) : (wide x).val = x.val := by
  exact AspisR1.ExtractedMaskReducer.cast_widen_value x

theorem source_success (w0 w1 w2 c0 c1 c2 : U32)
    (hw0 : w0.val < P) (hw1 : w1.val < P) (hw2 : w2.val < P)
    (hc0 : c0.val < P) (hc1 : c1.val < P) (hc2 : c2.val < P) :
    ∃ out : field.M31,
      state_only_poseidon.interpolate_three_constant_limb w0 w1 w2 c0 c1 c2 = .ok out ∧
      out.val < P ∧ out.val = (w0.val*c0.val+w1.val*c1.val+w2.val*c2.val) % P := by
  have hp0 : w0.val*c0.val < P*P := Nat.mul_lt_mul_of_lt_of_lt hw0 hc0
  have hp1 : w1.val*c1.val < P*P := Nat.mul_lt_mul_of_lt_of_lt hw1 hc1
  have hp2 : w2.val*c2.val < P*P := Nat.mul_lt_mul_of_lt_of_lt hw2 hc2
  have hbudget : 3*(P*P) < 2^64 := by norm_num [P]
  have hb0 : (wide w0).val*(wide c0).val < 2^64 := by rw [wide_value,wide_value]; omega
  have hb1 : (wide w1).val*(wide c1).val < 2^64 := by rw [wide_value,wide_value]; omega
  have hb2 : (wide w2).val*(wide c2).val < 2^64 := by rw [wide_value,wide_value]; omega
  obtain ⟨p0,hp0run,hp0val⟩ := mul_success (wide w0) (wide c0) hb0
  obtain ⟨p1,hp1run,hp1val⟩ := mul_success (wide w1) (wide c1) hb1
  obtain ⟨p2,hp2run,hp2val⟩ := mul_success (wide w2) (wide c2) hb2
  rw [wide_value,wide_value] at hp0val hp1val hp2val
  have hs01 : p0.val+p1.val < 2^64 := by rw [hp0val,hp1val]; omega
  obtain ⟨s01,hs01run,hs01val⟩ := add_success p0 p1 hs01
  have hstotal : s01.val+p2.val < 2^64 := by rw [hs01val,hp0val,hp1val,hp2val]; omega
  obtain ⟨total,htotalrun,htotalval⟩ := add_success s01 p2 hstotal
  obtain ⟨out,hreduce,hmod,hcanon⟩ := AspisR1.ExtractedMaskReducer.current_wrapper_mod total
  refine ⟨out,?_,hcanon,?_⟩
  · change (do
      let p0 ← UScalar.mul (wide w0) (wide c0)
      let p1 ← UScalar.mul (wide w1) (wide c1)
      let s01 ← UScalar.add p0 p1
      let p2 ← UScalar.mul (wide w2) (wide c2)
      let total ← UScalar.add s01 p2
      field.M31.reduce_u64 total) = .ok out
    simp only [hp0run,hp1run,hs01run,hp2run,htotalrun,hreduce,bind_tc_ok]
  · rw [hmod,htotalval,hs01val,hp0val,hp1val,hp2val]

abbrev M := AspisV8R15.ExactTowerBase.M31Exact

theorem source_model (w0 w1 w2 c0 c1 c2 : U32)
    (hw0 : w0.val < P) (hw1 : w1.val < P) (hw2 : w2.val < P)
    (hc0 : c0.val < P) (hc1 : c1.val < P) (hc2 : c2.val < P) :
    ∃ out : field.M31,
      state_only_poseidon.interpolate_three_constant_limb w0 w1 w2 c0 c1 c2 = .ok out ∧
      out.val < P ∧ (out.val : M) =
        (w0.val : M)*(c0.val : M)+(w1.val : M)*(c1.val : M)+(w2.val : M)*(c2.val : M) := by
  obtain ⟨out,hrun,hcanon,hmod⟩ := source_success w0 w1 w2 c0 c1 c2 hw0 hw1 hw2 hc0 hc1 hc2
  refine ⟨out,hrun,hcanon,?_⟩
  rw [hmod]
  simp only [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul]

#print axioms source_model
#print axioms wide_value
#print axioms source_success
end AspisR1.PoseidonThreeConstantLimb
