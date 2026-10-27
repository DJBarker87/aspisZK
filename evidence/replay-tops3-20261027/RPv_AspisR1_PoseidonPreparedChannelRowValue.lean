import RPv_AspisR1_PoseidonPreparedFieldArithmetic
import RPv_AspisR1PoseidonPreparedChannelArraySpecs
import ExtractedMaskM31AddSub
import ExtractedMaskReducer
import RPv_PoseidonPreparedSum3Source

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedChannelRowValue
open Aeneas.Std Result AspisR1SelectedMaskProbe
open AspisV8R15.ExactTowerBase AspisR1PoseidonPreparedSum3Source

abbrev M := M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev U64 := UScalar UScalarTy.U64
abbrev Row := Array U64 3#usize
abbrev CM := field.CM31
abbrev CanonicalCM := AspisR1.ExtractedMaskTowerAdd.CanonicalCM

def rowModel (r0 r1 r2 : U64) : CMExact :=
  ⟨(r0.val : M) - (r1.val : M),
   (r2.val : M) - (r0.val : M) - (r1.val : M)⟩

private theorem m31_sub_decode_canonical (x y : field.M31)
    (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, field.M31.sub x y = .ok z ∧ z.val < 2147483647 ∧
      AspisR1.PoseidonPreparedFieldArithmetic.decodeM z =
        AspisR1.PoseidonPreparedFieldArithmetic.decodeM x -
          AspisR1.PoseidonPreparedFieldArithmetic.decodeM y := by
  obtain ⟨z, hz, _, hcan⟩ := AspisR1.ExtractedMaskM31AddSub.current_sub_mod x y hx hy
  obtain ⟨z', hz', hdecode⟩ := AspisR1.PoseidonPreparedFieldArithmetic.m31_sub_decode x y hx hy
  have heq : z = z' := Result.ok.inj (hz.symm.trans hz')
  subst z'
  exact ⟨z, hz, hcan, hdecode⟩

theorem row_call_value (row : Row) :
    ∃ r0 r1 r2 out,
      Array.index_usize row 0#usize = .ok r0 ∧
      Array.index_usize row 1#usize = .ok r1 ∧
      Array.index_usize row 2#usize = .ok r2 ∧
      field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call
        () row = .ok out ∧ CanonicalCM out ∧
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM out = rowModel r0 r1 r2 := by
  obtain ⟨r0, hr0, _⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok row 0#usize (by scalar_tac)
  obtain ⟨r1, hr1, _⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok row 1#usize (by scalar_tac)
  obtain ⟨r2, hr2, _⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok row 2#usize (by scalar_tac)
  obtain ⟨m0, hm0, hv0, hc0⟩ := AspisR1.ExtractedMaskReducer.current_wrapper_mod r0
  obtain ⟨m1, hm1, hv1, hc1⟩ := AspisR1.ExtractedMaskReducer.current_wrapper_mod r1
  obtain ⟨m2, hm2, hv2, hc2⟩ := AspisR1.ExtractedMaskReducer.current_wrapper_mod r2
  obtain ⟨a, ha, hca, hda⟩ := m31_sub_decode_canonical m0 m1 hc0 hc1
  obtain ⟨b0, hb0, hcb0, hdb0⟩ := m31_sub_decode_canonical m2 m0 hc2 hc0
  obtain ⟨b, hb, hcb, hdb⟩ := m31_sub_decode_canonical b0 m1 hcb0 hc1
  have hd0 : AspisR1.PoseidonPreparedFieldArithmetic.decodeM m0 = (r0.val : M) := by
    change (m0.val : M) = (r0.val : M)
    rw [hv0, ZMod.natCast_mod]
  have hd1 : AspisR1.PoseidonPreparedFieldArithmetic.decodeM m1 = (r1.val : M) := by
    change (m1.val : M) = (r1.val : M)
    rw [hv1, ZMod.natCast_mod]
  have hd2 : AspisR1.PoseidonPreparedFieldArithmetic.decodeM m2 = (r2.val : M) := by
    change (m2.val : M) = (r2.val : M)
    rw [hv2, ZMod.natCast_mod]
  have hda' : AspisR1.PoseidonPreparedFieldArithmetic.decodeM a =
      (r0.val : M) - (r1.val : M) := by rw [hda, hd0, hd1]
  have hdb0' : AspisR1.PoseidonPreparedFieldArithmetic.decodeM b0 =
      (r2.val : M) - (r0.val : M) := by rw [hdb0, hd2, hd0]
  have hdb' : AspisR1.PoseidonPreparedFieldArithmetic.decodeM b =
      (r2.val : M) - (r0.val : M) - (r1.val : M) := by rw [hdb, hdb0', hd1]
  refine ⟨r0, r1, r2, ⟨a, b⟩, hr0, hr1, hr2, ?_, ⟨hca, hcb⟩, ?_⟩
  · simp only [field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
      hr0, hr1, hr2, hm0, hm1, hm2, ha, hb0, hb, bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · change AspisR1.PoseidonPreparedFieldArithmetic.decodeM a =
        (r0.val : M) - (r1.val : M)
      exact hda'
    · change AspisR1.PoseidonPreparedFieldArithmetic.decodeM b =
        (r2.val : M) - (r0.val : M) - (r1.val : M)
      exact hdb'

#print axioms row_call_value
end AspisR1.PoseidonPreparedChannelRowValue
