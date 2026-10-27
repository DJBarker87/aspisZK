import RPv_AspisR1_PoseidonPreparedChannelRowValue
import RPv_AspisR1_PoseidonPreparedFieldArithmetic
import RPv_PoseidonPreparedSum3Source

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedKaratsubaValue
open Aeneas.Std Result AspisR1SelectedMaskProbe
open AspisV8R15.ExactTowerBase AspisR1PoseidonPreparedSum3Source

abbrev U64 := UScalar UScalarTy.U64
abbrev QM := field.QM31
abbrev CM := field.CM31
abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev QMExact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev CanonicalCM := AspisR1.ExtractedMaskTowerAdd.CanonicalCM
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

def decodeQM (q : QM) : QMExact := ⟨AspisR1.PoseidonPreparedFieldArithmetic.decodeCM q.c0,
  AspisR1.PoseidonPreparedFieldArithmetic.decodeCM q.c1⟩

private theorem cm_add_decode_canonical (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    ∃ z, field.CM31.add x y = .ok z ∧ CanonicalCM z ∧
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM z =
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM x +
          AspisR1.PoseidonPreparedFieldArithmetic.decodeCM y := by
  obtain ⟨z, hz, hcan, _, _⟩ := AspisR1.ExtractedMaskTowerAdd.current_cm_add_mod x y hx hy
  obtain ⟨z', hz', hval⟩ := AspisR1.PoseidonPreparedFieldArithmetic.cm_add_decode x y hx hy
  have heq : z = z' := Result.ok.inj (hz.symm.trans hz')
  subst z'
  exact ⟨z, hz, hcan, hval⟩

private theorem cm_sub_decode_canonical (x y : CM) (hx : CanonicalCM x) (hy : CanonicalCM y) :
    ∃ z, field.CM31.sub x y = .ok z ∧ CanonicalCM z ∧
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM z =
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM x -
          AspisR1.PoseidonPreparedFieldArithmetic.decodeCM y := by
  obtain ⟨z, hz, hcan, _, _⟩ := AspisR1.ExtractedMaskTowerAdd.current_cm_sub_mod x y hx hy
  obtain ⟨z', hz', hval⟩ := AspisR1.PoseidonPreparedFieldArithmetic.cm_sub_decode x y hx hy
  have heq : z = z' := Result.ok.inj (hz.symm.trans hz')
  subst z'
  exact ⟨z, hz, hcan, hval⟩

private theorem row_decode (row : Array U64 3#usize) :
    ∃ r0 r1 r2 out : _,
      Array.index_usize row 0#usize = .ok r0 ∧
      Array.index_usize row 1#usize = .ok r1 ∧
      Array.index_usize row 2#usize = .ok r2 ∧
      field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () row = .ok out ∧
      CanonicalCM out ∧
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM out =
        AspisR1.PoseidonPreparedChannelRowValue.rowModel r0 r1 r2 := by
  obtain ⟨r0, r1, r2, out, hr0, hr1, hr2, hrun, hcan, hval⟩ :=
    AspisR1.PoseidonPreparedChannelRowValue.row_call_value row
  exact ⟨r0, r1, r2, out, hr0, hr1, hr2, hrun, hcan, hval⟩

theorem converter_value (sums : Sums) :
    ∃ row0 row1 row2 r00 r01 r02 r10 r11 r12 r20 r21 r22 m0 m1 m2 out,
      Array.index_usize sums 0#usize = .ok row0 ∧
      Array.index_usize sums 1#usize = .ok row1 ∧
      Array.index_usize sums 2#usize = .ok row2 ∧
      Array.index_usize row0 0#usize = .ok r00 ∧ Array.index_usize row0 1#usize = .ok r01 ∧ Array.index_usize row0 2#usize = .ok r02 ∧
      Array.index_usize row1 0#usize = .ok r10 ∧ Array.index_usize row1 1#usize = .ok r11 ∧ Array.index_usize row1 2#usize = .ok r12 ∧
      Array.index_usize row2 0#usize = .ok r20 ∧ Array.index_usize row2 1#usize = .ok r21 ∧ Array.index_usize row2 2#usize = .ok r22 ∧
      field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () row0 = .ok m0 ∧
      field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () row1 = .ok m1 ∧
      field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () row2 = .ok m2 ∧
      CanonicalCM m0 ∧ CanonicalCM m1 ∧ CanonicalCM m2 ∧
      field.qm31_from_karatsuba_channel_sums sums = .ok out ∧ CanonicalQM out ∧
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM m0 =
        AspisR1.PoseidonPreparedChannelRowValue.rowModel r00 r01 r02 ∧
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM m1 =
        AspisR1.PoseidonPreparedChannelRowValue.rowModel r10 r11 r12 ∧
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM m2 =
        AspisR1.PoseidonPreparedChannelRowValue.rowModel r20 r21 r22 ∧
      decodeQM out = ⟨AspisR1.PoseidonPreparedChannelRowValue.rowModel r00 r01 r02 +
          (⟨2,1⟩ : CMExact) * AspisR1.PoseidonPreparedChannelRowValue.rowModel r10 r11 r12,
        AspisR1.PoseidonPreparedChannelRowValue.rowModel r20 r21 r22 -
          AspisR1.PoseidonPreparedChannelRowValue.rowModel r00 r01 r02 -
          AspisR1.PoseidonPreparedChannelRowValue.rowModel r10 r11 r12⟩ := by
  obtain ⟨row0, hr0, _⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok sums 0#usize (by scalar_tac)
  obtain ⟨row1, hr1, _⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok sums 1#usize (by scalar_tac)
  obtain ⟨row2, hr2, _⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok sums 2#usize (by scalar_tac)
  obtain ⟨r00, r01, r02, m0, hr00, hr01, hr02, hm0, hcan0, hv0⟩ := row_decode row0
  obtain ⟨r10, r11, r12, m1, hr10, hr11, hr12, hm1, hcan1, hv1⟩ := row_decode row1
  obtain ⟨r20, r21, r22, m2, hr20, hr21, hr22, hm2, hcan2, hv2⟩ := row_decode row2
  obtain ⟨r, hr, hrcan, hrv⟩ := AspisR1.PoseidonPreparedFieldArithmetic.mul_by_r_decode m1 hcan1
  obtain ⟨c0, hc0, hc0can, hc0v⟩ := cm_add_decode_canonical m0 r hcan0 hrcan
  obtain ⟨d0, hd0, hd0can, hd0v⟩ := cm_sub_decode_canonical m2 m0 hcan2 hcan0
  obtain ⟨d, hd, hdcan, hdv⟩ := cm_sub_decode_canonical d0 m1 hd0can hcan1
  let out : QM := { c0 := c0, c1 := d }
  have hrun : field.qm31_from_karatsuba_channel_sums sums = .ok out := by
    simp only [field.qm31_from_karatsuba_channel_sums, hr0, hr1, hr2,
      hm0, hm1, hm2, hr, hc0, hd0, hd, bind_tc_ok]
    rfl
  have hcanonical : CanonicalQM out := ⟨hc0can, hdcan⟩
  have hvalue0 : AspisR1.PoseidonPreparedFieldArithmetic.decodeCM m0 =
      AspisR1.PoseidonPreparedChannelRowValue.rowModel r00 r01 r02 := hv0
  have hvalue1 : AspisR1.PoseidonPreparedFieldArithmetic.decodeCM m1 =
      AspisR1.PoseidonPreparedChannelRowValue.rowModel r10 r11 r12 := hv1
  have hvalue2 : AspisR1.PoseidonPreparedFieldArithmetic.decodeCM m2 =
      AspisR1.PoseidonPreparedChannelRowValue.rowModel r20 r21 r22 := hv2
  have hvalue : decodeQM out =
      ⟨AspisR1.PoseidonPreparedChannelRowValue.rowModel r00 r01 r02 +
          (⟨2,1⟩ : CMExact) * AspisR1.PoseidonPreparedChannelRowValue.rowModel r10 r11 r12,
        AspisR1.PoseidonPreparedChannelRowValue.rowModel r20 r21 r22 -
          AspisR1.PoseidonPreparedChannelRowValue.rowModel r00 r01 r02 -
          AspisR1.PoseidonPreparedChannelRowValue.rowModel r10 r11 r12⟩ := by
    apply QuadraticAlgebra.ext
    · change AspisR1.PoseidonPreparedFieldArithmetic.decodeCM c0 = _
      rw [hc0v, hrv, hvalue0, hvalue1]
    · change AspisR1.PoseidonPreparedFieldArithmetic.decodeCM d = _
      rw [hdv, hd0v, hvalue2, hvalue0, hvalue1]
  exact ⟨row0,row1,row2,r00,r01,r02,r10,r11,r12,r20,r21,r22,m0,m1,m2,out,
    hr0,hr1,hr2,hr00,hr01,hr02,hr10,hr11,hr12,hr20,hr21,hr22,
    hm0,hm1,hm2,hcan0,hcan1,hcan2,hrun,hcanonical,hvalue0,hvalue1,hvalue2,hvalue⟩

#print axioms converter_value
end AspisR1.PoseidonPreparedKaratsubaValue
