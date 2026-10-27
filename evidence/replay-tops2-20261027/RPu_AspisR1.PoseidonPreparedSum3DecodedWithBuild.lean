import RPu_AspisR1PoseidonPreparedIndexActualLoopBuild
import RPu_AspisR1.PoseidonPreparedPrefixField
import RPu_AspisR1.PoseidonPreparedKaratsubaValue

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedSum3DecodedWithBuild
open Aeneas.Std Result AspisR1SelectedMaskProbe
open AspisV8R15.ExactTowerBase AspisR1PoseidonPreparedSum3Source

abbrev U64 := UScalar UScalarTy.U64
abbrev QM := field.QM31
abbrev CM := field.CM31
abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev QMExact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev PreparedArray := Array field.PreparedQm31Multiplier 3#usize
abbrev RightArray := Array QM 3#usize
abbrev Components := Array (Array field.M31 3#usize) 3#usize
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

private def rightAt (right : RightArray) (i : Fin 3) : QM :=
  right.val[(AspisR1PoseidonPreparedIndexProductBounds.uFin i).val]'(by
    have hu := AspisR1PoseidonPreparedIndexProductBounds.uFin_val i
    simpa [right.property, hu] using i.isLt)

private def zeroRow : Array U64 3#usize := Array.repeat 3#usize 0#u64
private def zeroSums : Sums := Array.repeat 3#usize zeroRow

private def decodeQM (q : QM) : QMExact := AspisR1.PoseidonPreparedKaratsubaValue.decodeQM q

private theorem zeroSums_cells :
    ∀ (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (AspisR1PoseidonPreparedIndexActualLoop.sumCell zeroSums c ch hc hch).val = 0 := by
  intro c ch hc hch
  have hcv : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
  have hchv : ch.val = 0 ∨ ch.val = 1 ∨ ch.val = 2 := by omega
  rcases hcv with h0 | h1 | h2 <;>
    rcases hchv with j0 | j1 | j2 <;>
    simp_all [zeroSums, zeroRow, AspisR1PoseidonPreparedIndexActualLoop.sumCell,
      AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell,
      AspisR1PoseidonPreparedChannelArraySet.at3, Array.repeat_val]
  all_goals norm_num

theorem actual_sum3_decoded
    (left : PreparedArray) (right : RightArray)
    (hleft : ∀ (i : Fin 3) (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (AspisR1PoseidonPreparedChannelRunStepLocal.at3
        (AspisR1PoseidonPreparedChannelRunStepLocal.at3
          (AspisR1PoseidonPreparedChannelRunStepLocal.at3 left
            (AspisR1PoseidonPreparedIndexProductBounds.uFin i)
            (by rw [AspisR1PoseidonPreparedIndexProductBounds.uFin_val]; exact i.isLt)).components c hc)
        ch hch).val < 2147483647)
    (hright : ∀ i : Fin 3,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (rightAt right i)) :
    ∃ tables : Fin 3 → Components, ∃ sums : Sums, ∃ out : QM,
      ∃ row0 row1 row2 r00 r01 r02 r10 r11 r12 r20 r21 r22 m0 m1 m2,
      AspisR1PoseidonPreparedIndexActualLoop.Loop
        { start := 0#usize, «end» := 3#usize } left right zeroSums = .ok sums ∧
      field.qm31_sum_products3_prepared left right = .ok out ∧ CanonicalQM out ∧
      decodeQM out = ⟨
        AspisR1.PoseidonPreparedChannelRowValue.rowModel r00 r01 r02 +
          (⟨2,1⟩ : CMExact) * AspisR1.PoseidonPreparedChannelRowValue.rowModel r10 r11 r12,
        AspisR1.PoseidonPreparedChannelRowValue.rowModel r20 r21 r22 -
          AspisR1.PoseidonPreparedChannelRowValue.rowModel r00 r01 r02 -
          AspisR1.PoseidonPreparedChannelRowValue.rowModel r10 r11 r12⟩ ∧
      Array.index_usize sums 0#usize = .ok row0 ∧
      Array.index_usize sums 1#usize = .ok row1 ∧
      Array.index_usize sums 2#usize = .ok row2 ∧
      Array.index_usize row0 0#usize = .ok r00 ∧ Array.index_usize row0 1#usize = .ok r01 ∧
      Array.index_usize row0 2#usize = .ok r02 ∧ Array.index_usize row1 0#usize = .ok r10 ∧
      Array.index_usize row1 1#usize = .ok r11 ∧ Array.index_usize row1 2#usize = .ok r12 ∧
      Array.index_usize row2 0#usize = .ok r20 ∧ Array.index_usize row2 1#usize = .ok r21 ∧
      Array.index_usize row2 2#usize = .ok r22 ∧
      field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () row0 = .ok m0 ∧
      field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () row1 = .ok m1 ∧
      field.qm31_from_karatsuba_channel_sums.closure.Insts.CoreOpsFunctionFnTupleArrayU643CM31.call () row2 = .ok m2 ∧
      (∀ (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3),
        ((AspisR1PoseidonPreparedIndexActualLoop.sumCell sums c ch hc hch).val : M) =
          AspisR1.PoseidonPreparedPrefixField.prefixField left tables 3 c ch hc hch) ∧
      (∀ i : Fin 3,
        (do
          let rightSum ← field.CM31.add (rightAt right i).c0 (rightAt right i).c1
          let m ← field.M31.add (rightAt right i).c0.a (rightAt right i).c0.b
          let m1 ← field.M31.add (rightAt right i).c1.a (rightAt right i).c1.b
          let m2 ← field.M31.add rightSum.a rightSum.b
          ok (Array.make 3#usize [
            (Array.make 3#usize [(rightAt right i).c0.a, (rightAt right i).c0.b, m] : Array field.M31 3#usize),
            (Array.make 3#usize [(rightAt right i).c1.a, (rightAt right i).c1.b, m1] : Array field.M31 3#usize),
            (Array.make 3#usize [rightSum.a, rightSum.b, m2] : Array field.M31 3#usize)] : Components)) = .ok (tables i)) := by
  obtain ⟨tables, sums, hloop, hvalues, hbuild⟩ :=
    AspisR1PoseidonPreparedIndexActualLoopBuild.actual_loop_success left right zeroSums
      hleft (by intro i; exact hright i) zeroSums_cells
  obtain ⟨sourceOut, hconvert, hcanonical⟩ :=
    AspisR1PoseidonPreparedKaratsubaSuccess.from_karatsuba_success sums
  have hsource : field.qm31_sum_products3_prepared left right = .ok sourceOut := by
    have hloop' : field.qm31_sum_products3_prepared_loop0
      { start := 0#usize, «end» := 3#usize } left right
      (Array.repeat 3#usize (Array.repeat 3#usize 0#u64)) = .ok sums := by
        simpa [zeroSums, zeroRow] using hloop
    simp only [field.qm31_sum_products3_prepared, hloop', hconvert, bind_tc_ok]
  obtain ⟨row0,row1,row2,r00,r01,r02,r10,r11,r12,r20,r21,r22,m0,m1,m2,out,
    hrow0,hrow1,hrow2,h00,h01,h02,h10,h11,h12,h20,h21,h22,
    hm0,hm1,hm2,hcan0,hcan1,hcan2,hconvert',hcanonical',
    hval0,hval1,hval2,hdecoded⟩ :=
      AspisR1.PoseidonPreparedKaratsubaValue.converter_value sums
  have hvalues' : ∀ (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3),
      ((AspisR1PoseidonPreparedIndexActualLoop.sumCell sums c ch hc hch).val : M) =
        AspisR1.PoseidonPreparedPrefixField.prefixField left tables 3 c ch hc hch := by
    intro c ch hc hch
    calc
      ((AspisR1PoseidonPreparedIndexActualLoop.sumCell sums c ch hc hch).val : M) =
          ((AspisR1PoseidonPreparedIndexActualLoopBuild.sumCell sums c ch hc hch).val : M) := by rfl
      _ = (AspisR1PoseidonPreparedIndexProductBounds.prefixProduct left tables 3 c ch hc hch : M) :=
        congrArg (fun n : Nat => (n : M)) (hvalues c ch hc hch)
      _ = AspisR1.PoseidonPreparedPrefixField.prefixField left tables 3 c ch hc hch :=
        AspisR1.PoseidonPreparedPrefixField.prefixProduct_cast left tables 3 c ch hc hch
  have hout : sourceOut = out := Result.ok.inj (hconvert.symm.trans hconvert')
  refine ⟨tables,sums,sourceOut,row0,row1,row2,r00,r01,r02,r10,r11,r12,r20,r21,r22,
    m0,m1,m2,hloop,hsource,hcanonical,?_,hrow0,hrow1,hrow2,h00,h01,h02,h10,h11,h12,
    h20,h21,h22,hm0,hm1,hm2,hvalues',hbuild⟩
  rw [hout]
  exact hdecoded

#print axioms actual_sum3_decoded
end AspisR1.PoseidonPreparedSum3DecodedWithBuild
