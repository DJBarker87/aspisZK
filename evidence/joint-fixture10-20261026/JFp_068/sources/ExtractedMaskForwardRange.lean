import AspisR1SelectedMaskProbe.Funs
import Aeneas.Std.RangeIter
import ExtractedMaskCoefficientStep

/-! Actual forward `Range Usize` iterator facts and their coefficient-body wrappers.
    The proof uses the retained Aeneas `RangeIter` WP specification; no loop
    iterations are unfolded here. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskForwardRange

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe

abbrev Range := core.ops.range.Range Usize

/-- At or beyond the end, the actual forward iterator returns `none` and the
    unchanged range. -/
theorem next_done (iter : Range) (hge : iter.start.val ≥ iter.end.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none, iter) := by
  obtain ⟨out, hrun, hspec⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_none_spec
      (partialOrdInst := core.cmp.PartialOrdUsize) (by intros; rfl) iter hge)
  rcases out with ⟨opt, iter1⟩
  rcases hspec with ⟨hopt, hiter⟩
  cases hopt
  cases hiter
  exact hrun

/-- Below the end, the actual forward iterator yields its old start and a
    successor range. The successor has the checked value `start+1`; it stays
    within Usize because the old start was below a representable end. -/
theorem next_step (iter : Range) (hlt : iter.start.val < iter.end.val) :
    ∃ iter1 : Range,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some iter.start, iter1) ∧
      iter1.start.val = iter.start.val + 1 ∧
      iter1.end = iter.end ∧
      iter.start.val + 1 ≤ Usize.max := by
  obtain ⟨out, hrun, hspec⟩ := WP.spec_imp_exists
    (Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_some_spec
      (cloneInst := core.clone.CloneUsize)
      (partialOrdInst := core.cmp.PartialOrdUsize)
      (by intros; rfl) (by intros; rfl) iter hlt)
  rcases out with ⟨opt, iter1⟩
  rcases hspec with ⟨hopt, hstart, hend⟩
  cases hopt
  have hbound : iter.start.val + 1 ≤ Usize.max := by
    have hb : iter.start.val + 1 < 2 ^ System.Platform.numBits := by
      simpa [Usize.numBits, UScalarTy.numBits, hstart] using iter1.start.hBounds
    have hb' : iter.start.val + 1 ≤ 2 ^ System.Platform.numBits - 1 := by omega
    simpa [Usize.max, Usize.numBits, UScalarTy.numBits] using hb'
  exact ⟨iter1, hrun, hstart, hend, hbound⟩

/-- Range-indexed wrapper for the first generated population body. -/
theorem loop0_body_step_from_range
    (c1 : AspisR1.ExtractedMaskCoefficientStep.C1)
    (iter : Range) (coefficients : AspisR1.ExtractedMaskCoefficientStep.Coefficients)
    (column : Usize)
    (hstart : iter.start.val = column.val) (hend : iter.end.val = 16)
    (hcolumn : column.val < 16)
    (hsource : ∀ j : Fin 16,
      AspisR1.ExtractedMaskCoefficientStep.CanonicalQM
        (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1 j))
    (hcoefficients : AspisR1.ExtractedMaskCoefficientStep.CanonicalArray coefficients) :
    ∃ transformed updated iter1,
      state_only_hiding.state_only_selected_mask_value_loop0.body
        c1 iter coefficients = .ok (.cont (iter1, updated)) ∧
      AspisR1.ExtractedMaskCoefficientStep.CanonicalQM transformed ∧
      AspisR1.ExtractedMaskQM31Exact.decode transformed =
        AspisR1.ExtractedMaskTowerBasisExact.basisElement (column.val % 4) *
          AspisR1.ExtractedMaskQM31Exact.decode
            (c1.val[column.val]'(by simpa [c1.property] using hcolumn)) ∧
      updated = coefficients.set
        (core.convert.num.FromUsizeU8.from
          (state_only_hiding.FACTOR_EXPONENTS.val[column.val]'
            (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn)))
        transformed ∧
      AspisR1.ExtractedMaskCoefficientStep.CanonicalArray updated := by
  have hlt : iter.start.val < iter.end.val := by omega
  obtain ⟨iter1, hnext, hinc, hend1, _⟩ := next_step iter hlt
  have hstartEq : iter.start = column := UScalar.eq_of_val_eq hstart
  have hnext' :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some column, iter1) := by simpa [hstartEq] using hnext
  obtain ⟨transformed, updated, hbody, htransform, hvalue, hupdated, hcanonical⟩ :=
    AspisR1.ExtractedMaskCoefficientStep.loop0_body_step c1 iter iter1
      coefficients column hnext' hcolumn hsource hcoefficients
  exact ⟨transformed, updated, iter1, hbody, htransform, hvalue, hupdated, hcanonical⟩

/-- Range-indexed wrapper for the second generated population body. -/
theorem loop1_body_step_from_range
    (maskOnly : AspisR1.ExtractedMaskCoefficientStep.MaskOnly)
    (iter : Range) (coefficients : AspisR1.ExtractedMaskCoefficientStep.Coefficients)
    (column : Usize)
    (hstart : iter.start.val = column.val) (hend : iter.end.val = 10)
    (hcolumn : column.val < 10)
    (hsource : ∀ j : Fin 10,
      AspisR1.ExtractedMaskCoefficientStep.CanonicalQM
        (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly j))
    (hcoefficients : AspisR1.ExtractedMaskCoefficientStep.CanonicalArray coefficients) :
    ∃ transformed updated iter1,
      state_only_hiding.state_only_selected_mask_value_loop1.body
        maskOnly iter coefficients = .ok (.cont (iter1, updated)) ∧
      AspisR1.ExtractedMaskCoefficientStep.CanonicalQM transformed ∧
      AspisR1.ExtractedMaskQM31Exact.decode transformed =
        AspisR1.ExtractedMaskTowerBasisExact.basisElement (column.val % 4) *
          AspisR1.ExtractedMaskQM31Exact.decode
            (maskOnly.val[column.val]'(by simpa [maskOnly.property] using hcolumn)) ∧
      updated = coefficients.set
        (core.convert.num.FromUsizeU8.from
          (state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.val[column.val]'
            (by simpa [state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.property] using hcolumn)))
        transformed ∧
      AspisR1.ExtractedMaskCoefficientStep.CanonicalArray updated := by
  have hlt : iter.start.val < iter.end.val := by omega
  obtain ⟨iter1, hnext, hinc, hend1, _⟩ := next_step iter hlt
  have hstartEq : iter.start = column := UScalar.eq_of_val_eq hstart
  have hnext' :
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
        .ok (some column, iter1) := by simpa [hstartEq] using hnext
  obtain ⟨transformed, updated, hbody, htransform, hvalue, hupdated, hcanonical⟩ :=
    AspisR1.ExtractedMaskCoefficientStep.loop1_body_step maskOnly iter iter1
      coefficients column hnext' hcolumn hsource hcoefficients
  exact ⟨transformed, updated, iter1, hbody, htransform, hvalue, hupdated, hcanonical⟩

#print axioms next_done
#print axioms next_step
#print axioms loop0_body_step_from_range
#print axioms loop1_body_step_from_range

end AspisR1.ExtractedMaskForwardRange
