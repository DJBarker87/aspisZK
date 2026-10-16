import AspisR1SelectedMaskProbe.Funs
import ExtractedMaskTowerBasisExact
import ExtractedMaskCoefficientSchedule
import ExtractedMaskCoefficientArray
import ExtractedMaskHornerStep

/-! Actual generated one-step and finished-body contracts for coefficient
population loops 0 and 1. Each one-step result is the source `Array.update`
written at its exact table exponent, with a pointwise canonicality invariant.
No full loop range is unfolded. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskCoefficientStep

open Aeneas Aeneas.Std Result ControlFlow
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskCoefficientArray

abbrev QM := field.QM31
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev Coefficients := Array QM 27#usize
abbrev C1 := Array QM 16#usize
abbrev MaskOnly := Array QM 10#usize

/-- A canonicality invariant over every coefficient cell. -/
def CanonicalArray (a : Coefficients) : Prop :=
  ∀ i : Fin 27, CanonicalQM (a.val[i.val]'(by
    simpa [a.property] using i.isLt))

def coefficientCell (a : Coefficients) (i : Fin 27) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

def c1Cell (a : C1) (i : Fin 16) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

def maskCell (a : MaskOnly) (i : Fin 10) : QM :=
  a.val[i.val]'(by simpa [a.property] using i.isLt)

private theorem array_update_success
    (a : Coefficients) (i : Usize) (x : QM) (h : i.val < a.length) :
    ∃ out : Coefficients,
      Array.update a i x = .ok out ∧ out = a.set i x := by
  obtain ⟨out, hrun, hset⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Array.update_spec a i x h)
  exact ⟨out, hrun, hset⟩

private theorem set_update_canonical
    (a : Coefficients) (i : Usize) (x : QM)
    (ha : CanonicalArray a) (hx : CanonicalQM x) :
    CanonicalArray (a.set i x) := by
  intro j
  have hj : j.val < a.val.length := by simpa using j.isLt
  have hjset : j.val < (a.val.set i.val x).length := by simpa using hj
  change CanonicalQM ((a.val.set i.val x)[j.val]'hjset)
  by_cases hsame : i.val = j.val
  · have hcell : (a.val.set i.val x)[j.val]'hjset = x := by
      have hself := List.getElem_set_self (l := a.val) (i := i.val) (a := x)
        (by simpa [hsame] using hjset)
      simpa [hsame] using hself
    rw [hcell]
    exact hx
  · have hcell : (a.val.set i.val x)[j.val]'hjset = a.val[j.val]'hj := by
      simpa using (List.getElem_set_ne (l := a.val) (i := i.val) (j := j.val)
        hsame hjset)
    rw [hcell]
    exact ha j

theorem loop0_body_done
    (c1 : C1) (iter : core.ops.range.Range Usize)
    (coefficients : Coefficients) (iter1 : core.ops.range.Range Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none, iter1)) :
    state_only_hiding.state_only_selected_mask_value_loop0.body
      c1 iter coefficients = .ok (.done coefficients) := by
  simp [state_only_hiding.state_only_selected_mask_value_loop0.body, hnext]

theorem loop1_body_done
    (maskOnly : MaskOnly) (iter : core.ops.range.Range Usize)
    (coefficients : Coefficients) (iter1 : core.ops.range.Range Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (none, iter1)) :
    state_only_hiding.state_only_selected_mask_value_loop1.body
      maskOnly iter coefficients = .ok (.done coefficients) := by
  simp [state_only_hiding.state_only_selected_mask_value_loop1.body, hnext]

theorem loop0_body_step
    (c1 : C1) (iter iter1 : core.ops.range.Range Usize)
    (coefficients : Coefficients) (column : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some column, iter1))
    (hcolumn : column.val < 16)
    (hsource : ∀ j : Fin 16, CanonicalQM (c1Cell c1 j))
    (hcoefficients : CanonicalArray coefficients) :
    ∃ transformed : QM, ∃ updated : Coefficients,
      state_only_hiding.state_only_selected_mask_value_loop0.body
        c1 iter coefficients = .ok (.cont (iter1, updated)) ∧
      CanonicalQM transformed ∧
      AspisR1.ExtractedMaskQM31Exact.decode transformed =
        AspisR1.ExtractedMaskTowerBasisExact.basisElement
          (column.val % 4) *
        AspisR1.ExtractedMaskQM31Exact.decode (c1.val[column.val]'(by
          simpa [c1.property] using hcolumn)) ∧
      updated = coefficients.set
        (core.convert.num.FromUsizeU8.from
          (state_only_hiding.FACTOR_EXPONENTS.val[column.val]'
            (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn)))
        transformed ∧
      CanonicalArray updated := by
  let j : Fin 16 := ⟨column.val, hcolumn⟩
  let q := c1.val[column.val]'(by simpa [c1.property] using hcolumn)
  let coordinate := column &&& 3#usize
  have hget : Array.index_usize c1 column = .ok q := by
    have h := AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
      c1 column (by simpa [c1.property] using hcolumn)
    simpa [q] using h
  have hq : CanonicalQM q := by
    simpa [q, c1Cell, j] using hsource j
  have hcoord : coordinate.val < 4 := by
    rw [AspisR1.ExtractedMaskCoefficientSchedule.column_and_three_eq_mod_four
      column hcolumn]
    exact Nat.mod_lt _ (by omega)
  obtain ⟨transformed, htransform, hcanonicalTransform, htransformValue⟩ :=
    AspisR1.ExtractedMaskTowerBasisExact.current_mul_tower_basis_exact
      q coordinate hq hcoord
  obtain ⟨tableValue, htable, htableValue⟩ :=
    AspisR1.ExtractedMaskCoefficientSchedule.factor_table_lookup column hcolumn
  let destination := core.convert.num.FromUsizeU8.from tableValue
  have hdestinationValue : destination.val = (c1Exponent j).val := by
    simpa [destination, core.convert.num.FromUsizeU8.from_val_eq] using
      htableValue
  have hdestination : destination.val < 27 := by
    rw [hdestinationValue]
    exact (c1Exponent j).isLt
  have hupdateBound : destination.val < coefficients.length := by
    simpa [coefficients.property] using hdestination
  obtain ⟨updated, hupdate, hset⟩ :=
    array_update_success coefficients destination transformed hupdateBound
  have hupdatedCanonical : CanonicalArray updated := by
    rw [hset]
    exact set_update_canonical coefficients destination transformed
      hcoefficients hcanonicalTransform
  have hfactorCell :
      state_only_hiding.FACTOR_EXPONENTS.val[column.val]'
        (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn) = tableValue := by
    apply UScalar.val_eq_imp
    calc
      (state_only_hiding.FACTOR_EXPONENTS.val[column.val]'
        (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn)).val =
          (c1Exponent j).val := by simpa [j] using
            AspisR1.ExtractedMaskCoefficientSchedule.factor_table_cell j
      _ = tableValue.val := htableValue.symm
  have hdestinationCell : destination = core.convert.num.FromUsizeU8.from
      (state_only_hiding.FACTOR_EXPONENTS.val[column.val]'
        (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn)) := by
    simp only [destination, hfactorCell]
  have hsetCell : updated = coefficients.set
      (core.convert.num.FromUsizeU8.from
        (state_only_hiding.FACTOR_EXPONENTS.val[column.val]'
          (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn))) transformed := by
    rw [hset, hdestinationCell]
  refine ⟨transformed, updated, ?_, hcanonicalTransform, ?_, hsetCell,
    hupdatedCanonical⟩
  · simp only [state_only_hiding.state_only_selected_mask_value_loop0.body,
      hnext, bind_tc_ok, hget, lift, coordinate, htransform, htable, destination, hupdate]
  · rw [htransformValue]
    simp only [j, coordinate,
      AspisR1.ExtractedMaskCoefficientSchedule.column_and_three_eq_mod_four
        column hcolumn]
    simpa [q]

theorem loop1_body_step
    (maskOnly : MaskOnly) (iter iter1 : core.ops.range.Range Usize)
    (coefficients : Coefficients) (column : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some column, iter1))
    (hcolumn : column.val < 10)
    (hsource : ∀ j : Fin 10, CanonicalQM (maskCell maskOnly j))
    (hcoefficients : CanonicalArray coefficients) :
    ∃ transformed : QM, ∃ updated : Coefficients,
      state_only_hiding.state_only_selected_mask_value_loop1.body
        maskOnly iter coefficients = .ok (.cont (iter1, updated)) ∧
      CanonicalQM transformed ∧
      AspisR1.ExtractedMaskQM31Exact.decode transformed =
        AspisR1.ExtractedMaskTowerBasisExact.basisElement
          (column.val % 4) *
        AspisR1.ExtractedMaskQM31Exact.decode (maskOnly.val[column.val]'(by
          simpa [maskOnly.property] using hcolumn)) ∧
      updated = coefficients.set
        (core.convert.num.FromUsizeU8.from
          (state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.val[column.val]'
            (by simpa [state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.property] using hcolumn)))
        transformed ∧
      CanonicalArray updated := by
  let j : Fin 10 := ⟨column.val, hcolumn⟩
  let q := maskOnly.val[column.val]'(by simpa [maskOnly.property] using hcolumn)
  let coordinate := column &&& 3#usize
  have hget : Array.index_usize maskOnly column = .ok q := by
    have h := AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
      maskOnly column (by simpa [maskOnly.property] using hcolumn)
    simpa [q] using h
  have hq : CanonicalQM q := by
    simpa [q, maskCell, j] using hsource j
  have hcoord : coordinate.val < 4 := by
    have hmod :=
      AspisR1.ExtractedMaskCoefficientSchedule.column_and_three_eq_mod_four
        column (by omega)
    rw [hmod]
    exact Nat.mod_lt _ (by omega)
  obtain ⟨transformed, htransform, hcanonicalTransform, htransformValue⟩ :=
    AspisR1.ExtractedMaskTowerBasisExact.current_mul_tower_basis_exact
      q coordinate hq hcoord
  obtain ⟨tableValue, htable, htableValue⟩ :=
    AspisR1.ExtractedMaskCoefficientSchedule.mask_factor_table_lookup
      column hcolumn
  let destination := core.convert.num.FromUsizeU8.from tableValue
  have hdestinationValue : destination.val = (maskExponent j).val := by
    simpa [destination, core.convert.num.FromUsizeU8.from_val_eq] using
      htableValue
  have hdestination : destination.val < 27 := by
    rw [hdestinationValue]
    exact (maskExponent j).isLt
  have hupdateBound : destination.val < coefficients.length := by
    simpa [coefficients.property] using hdestination
  obtain ⟨updated, hupdate, hset⟩ :=
    array_update_success coefficients destination transformed hupdateBound
  have hupdatedCanonical : CanonicalArray updated := by
    rw [hset]
    exact set_update_canonical coefficients destination transformed
      hcoefficients hcanonicalTransform
  have hmaskCell :
      state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.val[column.val]'
        (by simpa [state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.property] using hcolumn) = tableValue := by
    apply UScalar.val_eq_imp
    calc
      (state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.val[column.val]'
        (by simpa [state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.property] using hcolumn)).val =
          (maskExponent j).val := by simpa [j] using
            AspisR1.ExtractedMaskCoefficientSchedule.mask_factor_table_cell j
      _ = tableValue.val := htableValue.symm
  have hdestinationCell : destination = core.convert.num.FromUsizeU8.from
      (state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.val[column.val]'
        (by simpa [state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.property] using hcolumn)) := by
    simp only [destination, hmaskCell]
  have hsetCell : updated = coefficients.set
      (core.convert.num.FromUsizeU8.from
        (state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.val[column.val]'
          (by simpa [state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.property] using hcolumn))) transformed := by
    rw [hset, hdestinationCell]
  refine ⟨transformed, updated, ?_, hcanonicalTransform, ?_, hsetCell,
    hupdatedCanonical⟩
  · simp only [state_only_hiding.state_only_selected_mask_value_loop1.body,
      hnext, bind_tc_ok, hget, lift, coordinate, htransform, htable, destination, hupdate]
  · rw [htransformValue]
    simp only [j, coordinate,
      AspisR1.ExtractedMaskCoefficientSchedule.column_and_three_eq_mod_four
        column (by omega)]
    simpa [q]

#print axioms array_update_success
#print axioms set_update_canonical
#print axioms loop0_body_done
#print axioms loop1_body_done
#print axioms loop0_body_step
#print axioms loop1_body_step

end AspisR1.ExtractedMaskCoefficientStep
