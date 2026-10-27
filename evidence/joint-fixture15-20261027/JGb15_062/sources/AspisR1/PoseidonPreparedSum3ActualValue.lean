import AspisR1.PoseidonPreparedSum3PreparedCallerWithBuild
import AspisR1.PoseidonPreparedProductCells
import AspisR1.PoseidonPreparedAccumulatorThree
import AspisR1.PoseidonPreparedSum3AccumulatorReads
import AspisR1.PoseidonPreparedConverterDecodedProducts
import AspisR1.PoseidonPreparedSum3ProductAlgebra
import PoseidonPreparedSum3Source
import ExtractedMaskPreparedState

set_option autoImplicit false
namespace AspisR1.PoseidonPreparedSum3ActualValue
open Aeneas.Std Result AspisR1SelectedMaskProbe
open AspisV8R15.ExactTowerBase AspisR1PoseidonPreparedSum3Source

abbrev M := AspisV8R15.ExactTowerBase.M31Exact
abbrev CMExact := AspisV8R15.ExactTowerBase.CM31Exact
abbrev QMExact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev PreparedArray := Array Prepared 3#usize
abbrev RightArray := Array QM 3#usize
abbrev Components := AspisR1.PoseidonPreparedSum3DecodedWithBuild.Components
abbrev Sums := AspisR1.PoseidonPreparedSum3DecodedWithBuild.Sums
abbrev U64 := UScalar UScalarTy.U64
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

private def decodeQM := AspisR1.PoseidonPreparedKaratsubaValue.decodeQM
private def leftAt (left : PreparedArray) (i : Fin 3) : Prepared :=
  left.val[(AspisR1PoseidonPreparedIndexProductBounds.uFin i).val]'(by
    have hu := AspisR1PoseidonPreparedIndexProductBounds.uFin_val i
    simpa [left.property, hu] using i.isLt)
private def rightAt (right : RightArray) (i : Fin 3) : QM :=
  right.val[(AspisR1PoseidonPreparedIndexProductBounds.uFin i).val]'(by
    have hu := AspisR1PoseidonPreparedIndexProductBounds.uFin_val i
    simpa [right.property, hu] using i.isLt)

private def i0 : Fin 3 := ⟨0, by omega⟩
private def i1 : Fin 3 := ⟨1, by omega⟩
private def i2 : Fin 3 := ⟨2, by omega⟩

/-- The exact successful prepared qmsum3 execution decodes to the sum of the
three QM31 input products used by its generated implementation. -/
theorem actual_sum3_value
    (left : PreparedArray) (right : RightArray)
    (hprepared : ∀ i : Fin 3, ∃ x : QM, CanonicalQM x ∧
      AspisR1.ExtractedMaskPreparedState.PreparedFor (leftAt left i) x)
    (hright : ∀ i : Fin 3,
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (rightAt right i)) :
    ∃ out : QM, ∃ x0 x1 x2 : QM,
      field.qm31_sum_products3_prepared left right = .ok out ∧ CanonicalQM out ∧
      AspisR1.ExtractedMaskPreparedState.PreparedFor (leftAt left i0) x0 ∧
      AspisR1.ExtractedMaskPreparedState.PreparedFor (leftAt left i1) x1 ∧
      AspisR1.ExtractedMaskPreparedState.PreparedFor (leftAt left i2) x2 ∧
      decodeQM out = decodeQM x0 * decodeQM (rightAt right i0) +
        decodeQM x1 * decodeQM (rightAt right i1) +
        decodeQM x2 * decodeQM (rightAt right i2) := by
  obtain ⟨x0,hx0,hp0⟩ := hprepared i0
  obtain ⟨x1,hx1,hp1⟩ := hprepared i1
  obtain ⟨x2,hx2,hp2⟩ := hprepared i2
  have hprepared' : ∀ i : Fin 3, ∃ x : QM, CanonicalQM x ∧
      AspisR1.ExtractedMaskPreparedState.PreparedFor (leftAt left i) x := hprepared
  obtain ⟨tables,sums,out,row0,row1,row2,r00,r01,r02,r10,r11,r12,r20,r21,r22,m0,m1,m2,
    hloop,hsource,hcanonical,hdecoded,hrow0,hrow1,hrow2,h00,h01,h02,h10,h11,h12,h20,h21,h22,
    hm0,hm1,hm2,hvalues,hbuild⟩ :=
    AspisR1.PoseidonPreparedSum3PreparedCallerWithBuild.actual_sum3_decoded_of_prepared
      left right hprepared' hright
  -- The source row cells are precisely the accumulator cells exposed by the
  -- checked reads in the generated converter.
  have hc00 : AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums 0#usize 0#usize
      (by scalar_tac) (by scalar_tac) = r00 :=
    AspisR1.PoseidonPreparedSum3AccumulatorReads.nested_read_eq_sumCell sums 0#usize 0#usize
      (by scalar_tac) (by scalar_tac) row0 r00 hrow0 h00
  have hc01 : AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums 0#usize 1#usize
      (by scalar_tac) (by scalar_tac) = r01 :=
    AspisR1.PoseidonPreparedSum3AccumulatorReads.nested_read_eq_sumCell sums 0#usize 1#usize
      (by scalar_tac) (by scalar_tac) row0 r01 hrow0 h01
  have hc02 : AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums 0#usize 2#usize
      (by scalar_tac) (by scalar_tac) = r02 :=
    AspisR1.PoseidonPreparedSum3AccumulatorReads.nested_read_eq_sumCell sums 0#usize 2#usize
      (by scalar_tac) (by scalar_tac) row0 r02 hrow0 h02
  have hc10 : AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums 1#usize 0#usize
      (by scalar_tac) (by scalar_tac) = r10 :=
    AspisR1.PoseidonPreparedSum3AccumulatorReads.nested_read_eq_sumCell sums 1#usize 0#usize
      (by scalar_tac) (by scalar_tac) row1 r10 hrow1 h10
  have hc11 : AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums 1#usize 1#usize
      (by scalar_tac) (by scalar_tac) = r11 :=
    AspisR1.PoseidonPreparedSum3AccumulatorReads.nested_read_eq_sumCell sums 1#usize 1#usize
      (by scalar_tac) (by scalar_tac) row1 r11 hrow1 h11
  have hc12 : AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums 1#usize 2#usize
      (by scalar_tac) (by scalar_tac) = r12 :=
    AspisR1.PoseidonPreparedSum3AccumulatorReads.nested_read_eq_sumCell sums 1#usize 2#usize
      (by scalar_tac) (by scalar_tac) row1 r12 hrow1 h12
  have hc20 : AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums 2#usize 0#usize
      (by scalar_tac) (by scalar_tac) = r20 :=
    AspisR1.PoseidonPreparedSum3AccumulatorReads.nested_read_eq_sumCell sums 2#usize 0#usize
      (by scalar_tac) (by scalar_tac) row2 r20 hrow2 h20
  have hc21 : AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums 2#usize 1#usize
      (by scalar_tac) (by scalar_tac) = r21 :=
    AspisR1.PoseidonPreparedSum3AccumulatorReads.nested_read_eq_sumCell sums 2#usize 1#usize
      (by scalar_tac) (by scalar_tac) row2 r21 hrow2 h21
  have hc22 : AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums 2#usize 2#usize
      (by scalar_tac) (by scalar_tac) = r22 :=
    AspisR1.PoseidonPreparedSum3AccumulatorReads.nested_read_eq_sumCell sums 2#usize 2#usize
      (by scalar_tac) (by scalar_tac) row2 r22 hrow2 h22

  have hb0 : AspisR1.PoseidonPreparedProductCells.rightBuilder (rightAt right i0) =
      .ok (tables i0) := by
    dsimp [AspisR1.PoseidonPreparedProductCells.rightBuilder] at hbuild ⊢
    exact hbuild i0
  have hb1 : AspisR1.PoseidonPreparedProductCells.rightBuilder (rightAt right i1) =
      .ok (tables i1) := by
    dsimp [AspisR1.PoseidonPreparedProductCells.rightBuilder] at hbuild ⊢
    exact hbuild i1
  have hb2 : AspisR1.PoseidonPreparedProductCells.rightBuilder (rightAt right i2) =
      .ok (tables i2) := by
    dsimp [AspisR1.PoseidonPreparedProductCells.rightBuilder] at hbuild ⊢
    exact hbuild i2
  have H0 := AspisR1.PoseidonPreparedProductCells.product_cells left tables right i0 x0 hp0 hx0 (hright i0) hb0
  have H1 := AspisR1.PoseidonPreparedProductCells.product_cells left tables right i1 x1 hp1 hx1 (hright i1) hb1
  have H2 := AspisR1.PoseidonPreparedProductCells.product_cells left tables right i2 x2 hp2 hx2 (hright i2) hb2
  dsimp at H0 H1 H2
  rcases H0 with ⟨p000,p001,p002,p010,p011,p012,p020,p021,p022⟩
  rcases H1 with ⟨p100,p101,p102,p110,p111,p112,p120,p121,p122⟩
  rcases H2 with ⟨p200,p201,p202,p210,p211,p212,p220,p221,p222⟩

  have hvaluesProduct : ∀ (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3),
      ((AspisR1PoseidonPreparedIndexActualLoopBuild.sumCell sums c ch hc hch).val : M) =
        AspisR1PoseidonPreparedIndexProductBounds.prefixProduct left tables 3 c ch hc hch := by
    intro c ch hc hch
    calc
      ((AspisR1PoseidonPreparedIndexActualLoopBuild.sumCell sums c ch hc hch).val : M) =
          AspisR1.PoseidonPreparedPrefixField.prefixField left tables 3 c ch hc hch := by
        simpa [AspisR1PoseidonPreparedIndexActualLoopBuild.sumCell,
          AspisR1PoseidonPreparedIndexActualLoop.sumCell] using hvalues c ch hc hch
      _ = AspisR1PoseidonPreparedIndexProductBounds.prefixProduct left tables 3 c ch hc hch :=
        (AspisR1.PoseidonPreparedPrefixField.prefixProduct_cast left tables 3 c ch hc hch).symm

  have sum3_cell (c ch : Usize) (hc : c.val < 3) (hch : ch.val < 3)
      (v : U64)
      (heq : AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums c ch hc hch = v) :
      (v.val : M) =
        ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i0 c ch hc hch : Nat) : M) +
        ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i1 c ch hc hch : Nat) : M) +
        ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i2 c ch hc hch : Nat) : M) := by
    calc
      (v.val : M) = ((AspisR1PoseidonPreparedChannelUpdateInvariantV2.sumCell sums c ch hc hch).val : M) := by
        exact congrArg (fun z : U64 => (z.val : M)) heq.symm
      _ = ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i0 c ch hc hch : Nat) : M) +
          ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i1 c ch hc hch : Nat) : M) +
          ((AspisR1PoseidonPreparedIndexProductBounds.product left tables i2 c ch hc hch : Nat) : M) := by
        simpa [i0, i1, i2, AspisR1PoseidonPreparedIndexActualLoopBuild.sumCell,
          AspisR1PoseidonPreparedIndexActualLoop.sumCell] using
          (AspisR1.PoseidonPreparedAccumulatorThree.accumulator_cell_three
            left tables sums hvaluesProduct c ch hc hch)
  have hacc00 := sum3_cell 0#usize 0#usize (by scalar_tac) (by scalar_tac) r00 hc00
  have hacc01 := sum3_cell 0#usize 1#usize (by scalar_tac) (by scalar_tac) r01 hc01
  have hacc02 := sum3_cell 0#usize 2#usize (by scalar_tac) (by scalar_tac) r02 hc02
  have hacc10 := sum3_cell 1#usize 0#usize (by scalar_tac) (by scalar_tac) r10 hc10
  have hacc11 := sum3_cell 1#usize 1#usize (by scalar_tac) (by scalar_tac) r11 hc11
  have hacc12 := sum3_cell 1#usize 2#usize (by scalar_tac) (by scalar_tac) r12 hc12
  have hacc20 := sum3_cell 2#usize 0#usize (by scalar_tac) (by scalar_tac) r20 hc20
  have hacc21 := sum3_cell 2#usize 1#usize (by scalar_tac) (by scalar_tac) r21 hc21
  have hacc22 := sum3_cell 2#usize 2#usize (by scalar_tac) (by scalar_tac) r22 hc22

  rw [p000, p100, p200] at hacc00
  rw [p001, p101, p201] at hacc01
  rw [p002, p102, p202] at hacc02
  rw [p010, p110, p210] at hacc10
  rw [p011, p111, p211] at hacc11
  rw [p012, p112, p212] at hacc12
  rw [p020, p120, p220] at hacc20
  rw [p021, p121, p221] at hacc21
  rw [p022, p122, p222] at hacc22

  have hacc00Norm : (r00.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = (x0.c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i0).c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x1.c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i1).c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x2.c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i2).c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) := by
    change (r00.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = (x0.c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i0).c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x1.c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i1).c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x2.c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i2).c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M)
    exact hacc00
  have hacc01Norm : (r01.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = (x0.c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i0).c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x1.c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i1).c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x2.c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i2).c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) := by
    change (r01.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = (x0.c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i0).c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x1.c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i1).c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x2.c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i2).c0.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M)
    exact hacc01
  have hacc10Norm : (r10.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = (x0.c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i0).c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x1.c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i1).c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x2.c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i2).c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) := by
    change (r10.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = (x0.c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i0).c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x1.c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i1).c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x2.c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i2).c1.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M)
    exact hacc10
  have hacc11Norm : (r11.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = (x0.c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i0).c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x1.c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i1).c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x2.c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i2).c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) := by
    change (r11.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = (x0.c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i0).c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x1.c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i1).c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      (x2.c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) * ((rightAt right i2).c1.b.val : AspisR1.PoseidonPreparedRowModelSumProducts.M)
    exact hacc11
  have hacc02Norm : (r02.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = ((x0.c0.a.val + x0.c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i0).c0.a.val + (rightAt right i0).c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x1.c0.a.val + x1.c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i1).c0.a.val + (rightAt right i1).c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x2.c0.a.val + x2.c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i2).c0.a.val + (rightAt right i2).c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) := by
    change (r02.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = ((x0.c0.a.val + x0.c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i0).c0.a.val + (rightAt right i0).c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x1.c0.a.val + x1.c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i1).c0.a.val + (rightAt right i1).c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x2.c0.a.val + x2.c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i2).c0.a.val + (rightAt right i2).c0.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M)
    exact hacc02
  have hacc12Norm : (r12.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = ((x0.c1.a.val + x0.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i0).c1.a.val + (rightAt right i0).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x1.c1.a.val + x1.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i1).c1.a.val + (rightAt right i1).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x2.c1.a.val + x2.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i2).c1.a.val + (rightAt right i2).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) := by
    change (r12.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = ((x0.c1.a.val + x0.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i0).c1.a.val + (rightAt right i0).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x1.c1.a.val + x1.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i1).c1.a.val + (rightAt right i1).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x2.c1.a.val + x2.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i2).c1.a.val + (rightAt right i2).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M)
    exact hacc12
  have hacc20Norm : (r20.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = ((x0.c0.a.val + x0.c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i0).c0.a.val + (rightAt right i0).c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x1.c0.a.val + x1.c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i1).c0.a.val + (rightAt right i1).c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x2.c0.a.val + x2.c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i2).c0.a.val + (rightAt right i2).c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) := by
    change (r20.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = ((x0.c0.a.val + x0.c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i0).c0.a.val + (rightAt right i0).c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x1.c0.a.val + x1.c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i1).c0.a.val + (rightAt right i1).c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x2.c0.a.val + x2.c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i2).c0.a.val + (rightAt right i2).c1.a.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M)
    exact hacc20
  have hacc21Norm : (r21.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = ((x0.c0.b.val + x0.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i0).c0.b.val + (rightAt right i0).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x1.c0.b.val + x1.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i1).c0.b.val + (rightAt right i1).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x2.c0.b.val + x2.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i2).c0.b.val + (rightAt right i2).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) := by
    change (r21.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) = ((x0.c0.b.val + x0.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i0).c0.b.val + (rightAt right i0).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x1.c0.b.val + x1.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i1).c0.b.val + (rightAt right i1).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
      ((x2.c0.b.val + x2.c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M) * (((rightAt right i2).c0.b.val + (rightAt right i2).c1.b.val) : AspisR1.PoseidonPreparedRowModelSumProducts.M)
    exact hacc21
  have hacc22Norm : (r22.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) =
      (((x0.c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) + x0.c1.a.val) +
        (x0.c0.b.val + x0.c1.b.val)) *
          (((rightAt right i0).c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
            (rightAt right i0).c1.a.val + ((rightAt right i0).c0.b.val + (rightAt right i0).c1.b.val)) +
      (((x1.c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) + x1.c1.a.val) +
        (x1.c0.b.val + x1.c1.b.val)) *
          (((rightAt right i1).c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
            (rightAt right i1).c1.a.val + ((rightAt right i1).c0.b.val + (rightAt right i1).c1.b.val)) +
      (((x2.c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) + x2.c1.a.val) +
        (x2.c0.b.val + x2.c1.b.val)) *
          (((rightAt right i2).c0.a.val : AspisR1.PoseidonPreparedRowModelSumProducts.M) +
            (rightAt right i2).c1.a.val + ((rightAt right i2).c0.b.val + (rightAt right i2).c1.b.val)) := by
    calc
      _ = (((x0.c0.a.val : M) + x0.c0.b.val) + x0.c1.a.val + x0.c1.b.val) *
          (((rightAt right i0).c0.a.val : M) + (rightAt right i0).c0.b.val + (rightAt right i0).c1.a.val + (rightAt right i0).c1.b.val) +
        (((x1.c0.a.val : M) + x1.c0.b.val) + x1.c1.a.val + x1.c1.b.val) *
          (((rightAt right i1).c0.a.val : M) + (rightAt right i1).c0.b.val + (rightAt right i1).c1.a.val + (rightAt right i1).c1.b.val) +
        (((x2.c0.a.val : M) + x2.c0.b.val) + x2.c1.a.val + x2.c1.b.val) *
          (((rightAt right i2).c0.a.val : M) + (rightAt right i2).c0.b.val + (rightAt right i2).c1.a.val + (rightAt right i2).c1.b.val) := by
            exact hacc22
      _ = _ := by ring

  have h0 : AspisR1.PoseidonPreparedChannelRowValue.rowModel r00 r01 r02 =
      (decodeQM x0).re * (decodeQM (rightAt right i0)).re +
      (decodeQM x1).re * (decodeQM (rightAt right i1)).re +
      (decodeQM x2).re * (decodeQM (rightAt right i2)).re := by
    have h := AspisR1.PoseidonPreparedRowModelSumProducts.rowModel_sum_three_products
      r00 r01 r02
      (x0.c0.a.val : M) (x0.c0.b.val : M) (x1.c0.a.val : M) (x1.c0.b.val : M)
      (x2.c0.a.val : M) (x2.c0.b.val : M)
      ((rightAt right i0).c0.a.val : M) ((rightAt right i0).c0.b.val : M)
      ((rightAt right i1).c0.a.val : M) ((rightAt right i1).c0.b.val : M)
      ((rightAt right i2).c0.a.val : M) ((rightAt right i2).c0.b.val : M)
      hacc00Norm
      hacc01Norm
      hacc02Norm
    simpa [decodeQM, AspisR1.PoseidonPreparedKaratsubaValue.decodeQM,
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
      AspisR1.PoseidonPreparedFieldArithmetic.decodeM] using h
  have h1 : AspisR1.PoseidonPreparedChannelRowValue.rowModel r10 r11 r12 =
      (decodeQM x0).im * (decodeQM (rightAt right i0)).im +
      (decodeQM x1).im * (decodeQM (rightAt right i1)).im +
      (decodeQM x2).im * (decodeQM (rightAt right i2)).im := by
    have h := AspisR1.PoseidonPreparedRowModelSumProducts.rowModel_sum_three_products
      r10 r11 r12
      (x0.c1.a.val : M) (x0.c1.b.val : M) (x1.c1.a.val : M) (x1.c1.b.val : M)
      (x2.c1.a.val : M) (x2.c1.b.val : M)
      ((rightAt right i0).c1.a.val : M) ((rightAt right i0).c1.b.val : M)
      ((rightAt right i1).c1.a.val : M) ((rightAt right i1).c1.b.val : M)
      ((rightAt right i2).c1.a.val : M) ((rightAt right i2).c1.b.val : M)
      hacc10Norm
      hacc11Norm
      hacc12Norm
    simpa [decodeQM, AspisR1.PoseidonPreparedKaratsubaValue.decodeQM,
      AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
      AspisR1.PoseidonPreparedFieldArithmetic.decodeM] using h
  have h2 : AspisR1.PoseidonPreparedChannelRowValue.rowModel r20 r21 r22 =
      ((decodeQM x0).re + (decodeQM x0).im) *
          ((decodeQM (rightAt right i0)).re + (decodeQM (rightAt right i0)).im) +
      ((decodeQM x1).re + (decodeQM x1).im) *
          ((decodeQM (rightAt right i1)).re + (decodeQM (rightAt right i1)).im) +
      ((decodeQM x2).re + (decodeQM x2).im) *
          ((decodeQM (rightAt right i2)).re + (decodeQM (rightAt right i2)).im) := by
    have h := AspisR1.PoseidonPreparedRowModelSumProducts.rowModel_sum_three_products
      r20 r21 r22
      ((x0.c0.a.val : M) + x0.c1.a.val) ((x0.c0.b.val : M) + x0.c1.b.val)
      ((x1.c0.a.val : M) + x1.c1.a.val) ((x1.c0.b.val : M) + x1.c1.b.val)
      ((x2.c0.a.val : M) + x2.c1.a.val) ((x2.c0.b.val : M) + x2.c1.b.val)
      (((rightAt right i0).c0.a.val : M) + (rightAt right i0).c1.a.val)
      (((rightAt right i0).c0.b.val : M) + (rightAt right i0).c1.b.val)
      (((rightAt right i1).c0.a.val : M) + (rightAt right i1).c1.a.val)
      (((rightAt right i1).c0.b.val : M) + (rightAt right i1).c1.b.val)
      (((rightAt right i2).c0.a.val : M) + (rightAt right i2).c1.a.val)
      (((rightAt right i2).c0.b.val : M) + (rightAt right i2).c1.b.val)
      hacc20Norm
      hacc21Norm
      hacc22Norm
    have hx0 : (⟨(x0.c0.a.val : M) + x0.c1.a.val,
        (x0.c0.b.val : M) + x0.c1.b.val⟩ : CMExact) =
        (decodeQM x0).re + (decodeQM x0).im := by
      apply QuadraticAlgebra.ext <;> simp [decodeQM,
        AspisR1.PoseidonPreparedKaratsubaValue.decodeQM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeM,
        QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    have hx1 : (⟨(x1.c0.a.val : M) + x1.c1.a.val,
        (x1.c0.b.val : M) + x1.c1.b.val⟩ : CMExact) =
        (decodeQM x1).re + (decodeQM x1).im := by
      apply QuadraticAlgebra.ext <;> simp [decodeQM,
        AspisR1.PoseidonPreparedKaratsubaValue.decodeQM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeM,
        QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    have hx2 : (⟨(x2.c0.a.val : M) + x2.c1.a.val,
        (x2.c0.b.val : M) + x2.c1.b.val⟩ : CMExact) =
        (decodeQM x2).re + (decodeQM x2).im := by
      apply QuadraticAlgebra.ext <;> simp [decodeQM,
        AspisR1.PoseidonPreparedKaratsubaValue.decodeQM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeM,
        QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    have hy0 : (⟨((rightAt right i0).c0.a.val : M) + (rightAt right i0).c1.a.val,
        ((rightAt right i0).c0.b.val : M) + (rightAt right i0).c1.b.val⟩ : CMExact) =
        (decodeQM (rightAt right i0)).re + (decodeQM (rightAt right i0)).im := by
      apply QuadraticAlgebra.ext <;> simp [decodeQM,
        AspisR1.PoseidonPreparedKaratsubaValue.decodeQM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeM,
        QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    have hy1 : (⟨((rightAt right i1).c0.a.val : M) + (rightAt right i1).c1.a.val,
        ((rightAt right i1).c0.b.val : M) + (rightAt right i1).c1.b.val⟩ : CMExact) =
        (decodeQM (rightAt right i1)).re + (decodeQM (rightAt right i1)).im := by
      apply QuadraticAlgebra.ext <;> simp [decodeQM,
        AspisR1.PoseidonPreparedKaratsubaValue.decodeQM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeM,
        QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    have hy2 : (⟨((rightAt right i2).c0.a.val : M) + (rightAt right i2).c1.a.val,
        ((rightAt right i2).c0.b.val : M) + (rightAt right i2).c1.b.val⟩ : CMExact) =
        (decodeQM (rightAt right i2)).re + (decodeQM (rightAt right i2)).im := by
      apply QuadraticAlgebra.ext <;> simp [decodeQM,
        AspisR1.PoseidonPreparedKaratsubaValue.decodeQM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeCM,
        AspisR1.PoseidonPreparedFieldArithmetic.decodeM,
        QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
    rw [hx0, hy0, hx1, hy1, hx2, hy2] at h
    exact h
  have hformula := AspisR1.PoseidonPreparedConverterDecodedProducts.converter_decoded_products
    out r00 r01 r02 r10 r11 r12 r20 r21 r22
    (decodeQM x0) (decodeQM x1) (decodeQM x2)
    (decodeQM (rightAt right i0)) (decodeQM (rightAt right i1)) (decodeQM (rightAt right i2))
    hdecoded h0 h1 h2
  exact ⟨out,x0,x1,x2,hsource,hcanonical,hp0,hp1,hp2,hformula⟩

#print axioms actual_sum3_value
end AspisR1.PoseidonPreparedSum3ActualValue
