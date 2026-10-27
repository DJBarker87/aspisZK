import RPu_AspisR1_PoseidonPreparedSum3DecodedWithBuild
import RPu_PoseidonPreparedSum3Source
import RPu_AspisR1PoseidonPreparedStateCells
import ExtractedMaskPreparedState

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedSum3PreparedCallerWithBuild
open Aeneas.Std Result AspisR1SelectedMaskProbe
open AspisR1.PoseidonPreparedSum3DecodedWithBuild
open AspisR1PoseidonPreparedSum3Source

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev PreparedArray := Array Prepared 3#usize
abbrev RightArray := Array QM 3#usize
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev Components := AspisR1.PoseidonPreparedSum3DecodedWithBuild.Components
abbrev Sums := AspisR1.PoseidonPreparedSum3DecodedWithBuild.Sums
private def zeroRow : Array (UScalar UScalarTy.U64) 3#usize := Array.repeat 3#usize 0#u64
private def zeroSums : Sums := Array.repeat 3#usize zeroRow
private def decodeQM (q : QM) : AspisV8R15.ExactTowerBase.QM31Exact :=
  AspisR1.PoseidonPreparedKaratsubaValue.decodeQM q

private def uFin (i : Fin 3) : Usize :=
  UScalar.ofNatCore i.val (by scalar_tac)

private theorem uFin_val (i : Fin 3) : (uFin i).val = i.val :=
  UScalar.ofNatCore_val_eq (by scalar_tac)

private def leftAt (left : PreparedArray) (i : Fin 3) : Prepared :=
  left.val[(uFin i).val]'(by
    have hu := uFin_val i
    simpa [left.property, hu] using i.isLt)

private def rightAt (right : RightArray) (i : Fin 3) : QM :=
  right.val[(uFin i).val]'(by
    have hu := uFin_val i
    simpa [right.property, hu] using i.isLt)

theorem actual_sum3_decoded_of_prepared
    (left : PreparedArray) (right : RightArray)
    (hprepared : ∀ i : Fin 3, ∃ x : QM, CanonicalQM x ∧
      AspisR1.ExtractedMaskPreparedState.PreparedFor (leftAt left i) x)
    (hright : ∀ i : Fin 3,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (rightAt right i)) :
    ∃ tables : Fin 3 → Components, ∃ sums : Sums, ∃ out : QM,
      ∃ row0 row1 row2 r00 r01 r02 r10 r11 r12 r20 r21 r22 m0 m1 m2,
      AspisR1PoseidonPreparedIndexActualLoop.Loop
        { start := 0#usize, «end» := 3#usize } left right zeroSums = .ok sums ∧
      field.qm31_sum_products3_prepared left right = .ok out ∧ CanonicalQM out ∧
      decodeQM out = ⟨
        AspisR1.PoseidonPreparedChannelRowValue.rowModel r00 r01 r02 +
          (⟨2,1⟩ : AspisV8R15.ExactTowerBase.CM31Exact) *
            AspisR1.PoseidonPreparedChannelRowValue.rowModel r10 r11 r12,
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
        ((AspisR1PoseidonPreparedIndexActualLoop.sumCell sums c ch hc hch).val :
          AspisV8R15.ExactTowerBase.M31Exact) =
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
  have hleft : ∀ (i : Fin 3) (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3),
      (AspisR1PoseidonPreparedChannelRunStepLocal.at3
        (AspisR1PoseidonPreparedChannelRunStepLocal.at3
          (AspisR1PoseidonPreparedChannelRunStepLocal.at3 left (uFin i)
            (by rw [uFin_val]; exact i.isLt)).components c hc) ch hch).val < 2147483647 := by
    intro i c ch hc hch
    obtain ⟨x,hx,hp⟩ := hprepared i
    exact AspisR1PoseidonPreparedStateCells.prepared_cells_canonical
      (leftAt left i) x hx hp c ch hc hch
  have hright' : ∀ i : Fin 3,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
        (rightAt right i) := by
    intro i
    exact hright i
  exact AspisR1.PoseidonPreparedSum3DecodedWithBuild.actual_sum3_decoded left right hleft hright'

#print axioms actual_sum3_decoded_of_prepared
end AspisR1.PoseidonPreparedSum3PreparedCallerWithBuild
