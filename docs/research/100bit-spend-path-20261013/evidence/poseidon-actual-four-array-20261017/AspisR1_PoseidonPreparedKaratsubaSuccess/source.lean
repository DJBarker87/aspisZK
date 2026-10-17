import PoseidonPreparedSum3Source
import AspisR1.PoseidonPreparedIndexActualLoop
import ExtractedMaskReducer
import ExtractedMaskTowerAdd
import ExtractedMaskM31AddSub
import AspisR1PoseidonPreparedChannelArraySpecs

set_option autoImplicit false
namespace AspisR1PoseidonPreparedKaratsubaSuccess
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1PoseidonPreparedSum3Source

abbrev U64 := UScalar UScalarTy.U64
abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev QM31 := field.QM31
abbrev CanonicalCM := AspisR1.ExtractedMaskTowerAdd.CanonicalCM
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev Sums := Array (Array U64 3#usize) 3#usize

private theorem row_call_success (row : Array U64 3#usize) :
    ∃ out : CM31,
      field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () row = .ok out ∧
      CanonicalCM out := by
  obtain ⟨r0, hr0, hr0value⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok row 0#usize (by scalar_tac)
  obtain ⟨r1, hr1, hr1value⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok row 1#usize (by scalar_tac)
  obtain ⟨r2, hr2, hr2value⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok row 2#usize (by scalar_tac)
  obtain ⟨m0, hm0, _, hcan0⟩ := AspisR1.ExtractedMaskReducer.current_wrapper_mod r0
  obtain ⟨m1, hm1, _, hcan1⟩ := AspisR1.ExtractedMaskReducer.current_wrapper_mod r1
  obtain ⟨m2, hm2, _, hcan2⟩ := AspisR1.ExtractedMaskReducer.current_wrapper_mod r2
  obtain ⟨a, ha, haValue, hacan⟩ := AspisR1.ExtractedMaskM31AddSub.current_sub_mod m0 m1 hcan0 hcan1
  obtain ⟨b0, hb0, hb0Value, hb0can⟩ := AspisR1.ExtractedMaskM31AddSub.current_sub_mod m2 m0 hcan2 hcan0
  obtain ⟨b, hb, hbValue, hbcan⟩ := AspisR1.ExtractedMaskM31AddSub.current_sub_mod b0 m1 hb0can hcan1
  refine ⟨{ a := a, b := b }, ?_, ⟨hacan, hbcan⟩⟩
  simp only [field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call,
    hr0, hr1, hr2, hm0, hm1, hm2, ha, hb0, hb, bind_tc_ok]

private theorem mul_by_r_success (x : CM31) (hx : CanonicalCM x) :
    ∃ out : CM31, field.mul_by_r x = .ok out ∧ CanonicalCM out := by
  obtain ⟨a2, ea2, _, ca2⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a x.a hx.1 hx.1
  obtain ⟨a, ea, _, ca⟩ := AspisR1.ExtractedMaskM31AddSub.current_sub_mod a2 x.b ca2 hx.2
  obtain ⟨b2, eb2, _, cb2⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.b x.b hx.2 hx.2
  obtain ⟨b, eb, _, cb⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a b2 hx.1 cb2
  refine ⟨{ a := a, b := b }, ?_, ⟨ca, cb⟩⟩
  simp only [field.mul_by_r, field.M31.double, ea2, ea, eb2, eb, bind_tc_ok]

theorem from_karatsuba_success (sums : Sums) :
    ∃ out : QM31, field.qm31_from_karatsuba_channel_sums sums = .ok out ∧ CanonicalQM out := by
  obtain ⟨row0, hrow0, _⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok sums 0#usize (by scalar_tac)
  obtain ⟨row1, hrow1, _⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok sums 1#usize (by scalar_tac)
  obtain ⟨row2, hrow2, _⟩ := AspisR1PoseidonPreparedChannelArraySpecs.index_ok sums 2#usize (by scalar_tac)
  obtain ⟨m0, hm0, hm0can⟩ := row_call_success row0
  obtain ⟨m1, hm1, hm1can⟩ := row_call_success row1
  obtain ⟨m2, hm2, hm2can⟩ := row_call_success row2
  obtain ⟨r, hr, hrcan⟩ := mul_by_r_success m1 hm1can
  obtain ⟨c0, hc0, hc0can, _⟩ := AspisR1.ExtractedMaskTowerAdd.current_cm_add_mod m0 r hm0can hrcan
  obtain ⟨d0, hd0, hd0can, _⟩ := AspisR1.ExtractedMaskTowerAdd.current_cm_sub_mod m2 m0 hm2can hm0can
  obtain ⟨d, hd, hdcan, _⟩ := AspisR1.ExtractedMaskTowerAdd.current_cm_sub_mod d0 m1 hd0can hm1can
  refine ⟨{ c0 := c0, c1 := d }, ?_, ⟨hc0can, hdcan⟩⟩
  simp only [field.qm31_from_karatsuba_channel_sums, hrow0, hrow1, hrow2,
    hm0, hm1, hm2, hr, hc0, hd0, hd, bind_tc_ok]

#print axioms row_call_success
#print axioms from_karatsuba_success
end AspisR1PoseidonPreparedKaratsubaSuccess
