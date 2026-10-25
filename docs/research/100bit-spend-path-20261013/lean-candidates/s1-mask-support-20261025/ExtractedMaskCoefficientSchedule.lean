import AspisR1SelectedMaskProbe.Funs
import ExtractedMaskCoefficientArray
import ExtractedMaskHornerStep

/-! Draft only: exact finite schedule facts for selected-mask coefficient population. -/

namespace AspisR1.ExtractedMaskCoefficientSchedule

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

open AspisR1.ExtractedMaskCoefficientArray

/-- The first schedule is the literal source table [0,2,...,26,13,25]. -/
theorem factor_table_cell (j : Fin 16) :
    (state_only_hiding.FACTOR_EXPONENTS.val[j.val]'
      (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using j.isLt)).val =
      (c1Exponent j).val := by
  fin_cases j <;> norm_num [state_only_hiding.FACTOR_EXPONENTS, c1Exponent, Array.make]

/-- The second schedule is the literal source table [1,3,5,7,9,11,15,17,19,21]. -/
theorem mask_factor_table_cell (j : Fin 10) :
    (state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.val[j.val]'
      (by simpa [state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.property] using j.isLt)).val =
      (maskExponent j).val := by
  fin_cases j <;> norm_num [state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS, maskExponent, Array.make]

/-- The actual Aeneas indexing operation returns a U8 whose value is the
    selected exponent. This uses the already checked generic array-read fact. -/
theorem factor_table_lookup (column : Usize) (hcolumn : column.val < 16) :
    ∃ x : U8, state_only_hiding.FACTOR_EXPONENTS.index_usize column = .ok x ∧
      x.val = (c1Exponent ⟨column.val, hcolumn⟩).val := by
  let j : Fin 16 := ⟨column.val, hcolumn⟩
  refine ⟨state_only_hiding.FACTOR_EXPONENTS.val[column.val]'
      (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn), ?_, ?_⟩
  · have hread := AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
      state_only_hiding.FACTOR_EXPONENTS column (by simpa using hcolumn)
    simpa [j] using hread
  · exact factor_table_cell j

/-- The second actual table lookup similarly returns its scheduled U8. -/
theorem mask_factor_table_lookup (column : Usize) (hcolumn : column.val < 10) :
    ∃ x : U8,
      state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.index_usize column = .ok x ∧
      x.val = (maskExponent ⟨column.val, hcolumn⟩).val := by
  let j : Fin 10 := ⟨column.val, hcolumn⟩
  refine ⟨state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.val[column.val]'
      (by simpa [state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.property] using hcolumn), ?_, ?_⟩
  · have hread := AspisR1.ExtractedMaskHornerStep.array_index_usize_ok
      state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS column (by simpa using hcolumn)
    simpa [j] using hread
  · exact mask_factor_table_cell j

/-- The U8-to-Usize conversion used by the extracted body preserves its value;
    thus every selected exponent remains a valid coefficient index. -/
theorem converted_exponent_bound (x : U8) (hx : x.val < 27) :
    (core.convert.num.FromUsizeU8.from x).val < 27 := by
  simpa [core.convert.num.FromUsizeU8.from_val_eq] using hx

/-- For every bounded source column, the extracted `column &&& 3` is its
    residue modulo four. This is a small bounded scalar fact, not a field proof. -/
theorem column_and_three_eq_mod_four (column : Usize) (hcolumn : column.val < 16) :
    (column &&& 3#usize).val = column.val % 4 := by
  have hv := UScalar.val_and column (3#usize)
  simp only [show (3#usize).val = 3 by rfl] at hv
  rw [hv]
  interval_cases h : column.val <;> norm_num at h <;> decide

/-- Each source schedule is injective, so no two writes in one loop overwrite
    an earlier loop cell. -/
theorem factor_schedule_injective : Function.Injective c1Exponent := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [c1Exponent]

theorem mask_schedule_injective : Function.Injective maskExponent := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [maskExponent]

/-- No mask-only destination overlaps a C1 destination. -/
theorem schedules_disjoint :
    ∀ a : Fin 16, ∀ b : Fin 10, c1Exponent a ≠ maskExponent b := by
  decide

/-- The schedules cover all coefficients 0..26 except coefficient 23. -/
theorem schedules_cover_except_23 (e : Fin 27) :
    (∃ a : Fin 16, c1Exponent a = e) ∨
      (∃ b : Fin 10, maskExponent b = e) ↔ e.val ≠ 23 := by
  fin_cases e <;> decide

#print axioms factor_table_cell
#print axioms mask_factor_table_cell
#print axioms factor_table_lookup
#print axioms mask_factor_table_lookup
#print axioms converted_exponent_bound
#print axioms column_and_three_eq_mod_four
#print axioms factor_schedule_injective
#print axioms mask_schedule_injective
#print axioms schedules_disjoint
#print axioms schedules_cover_except_23

end AspisR1.ExtractedMaskCoefficientSchedule
