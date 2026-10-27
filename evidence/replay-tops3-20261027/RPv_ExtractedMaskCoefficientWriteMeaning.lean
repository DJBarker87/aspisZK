import RPv_ExtractedMaskCoefficientDecode
import ExtractedMaskCoefficientLoop0
import ExtractedMaskCoefficientLoop1

/-! Draft only: connect each actual generated coefficient-body model write to a
single decoded finite-field `Function.update`. Inputs must be canonical only
because the extracted basis multiplication correctness theorem requires that
source-cell condition; no invariant on the other coefficient cells is needed. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskCoefficientWriteMeaning

open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskCoefficientArray
open AspisR1.ExtractedMaskCoefficientSchedule

abbrev QM := field.QM31
abbrev C1 := AspisR1.ExtractedMaskCoefficientStep.C1
abbrev MaskOnly := AspisR1.ExtractedMaskCoefficientStep.MaskOnly
abbrev Coefficients := AspisR1.ExtractedMaskCoefficientStep.Coefficients
abbrev CanonicalQM := AspisR1.ExtractedMaskCoefficientStep.CanonicalQM
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

/-- One C1 write changes the decoded coefficient function at exactly the
C1 schedule destination, with the exact basis-transformed source value. -/
theorem decoded_writeAt0
    (c1 : C1) (coefficients : Coefficients) (column : Usize)
    (hcolumn : column.val < 16)
    (hsource : CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1
        ⟨column.val, hcolumn⟩)) :
    AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients
        (AspisR1.ExtractedMaskCoefficientLoop0.writeAt0
          c1 coefficients column hcolumn) =
      Function.update
        (AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients coefficients)
        (c1Exponent ⟨column.val, hcolumn⟩)
        (AspisR1.ExtractedMaskTowerBasisExact.basisElement (column.val % 4) *
          AspisR1.ExtractedMaskQM31Exact.decode
            (AspisR1.ExtractedMaskCoefficientStep.c1Cell c1
              ⟨column.val, hcolumn⟩)) := by
  let j : Fin 16 := ⟨column.val, hcolumn⟩
  let q : QM := c1.val[column.val]'(by simpa [c1.property] using hcolumn)
  have hq : CanonicalQM q := by
    simpa [q, AspisR1.ExtractedMaskCoefficientStep.c1Cell, j] using hsource
  let coordinate := column &&& 3#usize
  have hcoord : coordinate.val < 4 := by
    rw [column_and_three_eq_mod_four column hcolumn]
    exact Nat.mod_lt _ (by omega)
  obtain ⟨z, hmul, _hzcanonical, hzvalue⟩ :=
    AspisR1.ExtractedMaskTowerBasisExact.current_mul_tower_basis_exact
      q coordinate hq hcoord
  have hzvalue' : AspisR1.ExtractedMaskQM31Exact.decode z =
      AspisR1.ExtractedMaskTowerBasisExact.basisElement (column.val % 4) *
        AspisR1.ExtractedMaskQM31Exact.decode q := by
    simpa [coordinate, column_and_three_eq_mod_four column hcolumn] using hzvalue
  let destination := core.convert.num.FromUsizeU8.from
    (state_only_hiding.FACTOR_EXPONENTS.val[column.val]'
      (by simpa [state_only_hiding.FACTOR_EXPONENTS.property] using hcolumn))
  have hdestination : destination.val = (c1Exponent j).val := by
    simpa [destination, core.convert.num.FromUsizeU8.from_val_eq] using
      factor_table_cell j
  have hset :
      AspisR1.ExtractedMaskCoefficientLoop0.writeAt0
        c1 coefficients column hcolumn = coefficients.set destination z := by
    simp [AspisR1.ExtractedMaskCoefficientLoop0.writeAt0,
      q, coordinate, destination, hmul]
  have hbound : destination.val < 27 := by
    rw [hdestination]
    exact (c1Exponent j).isLt
  have hfin : (⟨destination.val, hbound⟩ : Fin 27) = c1Exponent j :=
    Fin.ext hdestination
  rw [hset, AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients_set
    coefficients destination z hbound, hfin, hzvalue']
  simp [j, q, AspisR1.ExtractedMaskCoefficientStep.c1Cell]

/-- One mask-only write changes the decoded coefficient function at exactly
the mask-only schedule destination, with the exact basis-transformed source. -/
theorem decoded_writeAt1
    (maskOnly : MaskOnly) (coefficients : Coefficients) (column : Usize)
    (hcolumn : column.val < 10)
    (hsource : CanonicalQM
      (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly
        ⟨column.val, hcolumn⟩)) :
    AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients
        (AspisR1.ExtractedMaskCoefficientLoop1.writeAt1
          maskOnly coefficients column hcolumn) =
      Function.update
        (AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients coefficients)
        (maskExponent ⟨column.val, hcolumn⟩)
        (AspisR1.ExtractedMaskTowerBasisExact.basisElement (column.val % 4) *
          AspisR1.ExtractedMaskQM31Exact.decode
            (AspisR1.ExtractedMaskCoefficientStep.maskCell maskOnly
              ⟨column.val, hcolumn⟩)) := by
  let j : Fin 10 := ⟨column.val, hcolumn⟩
  let q : QM := maskOnly.val[column.val]'(by simpa [maskOnly.property] using hcolumn)
  have hq : CanonicalQM q := by
    simpa [q, AspisR1.ExtractedMaskCoefficientStep.maskCell, j] using hsource
  let coordinate := column &&& 3#usize
  have hcoord : coordinate.val < 4 := by
    rw [column_and_three_eq_mod_four column (by omega : column.val < 16)]
    exact Nat.mod_lt _ (by omega)
  obtain ⟨z, hmul, _hzcanonical, hzvalue⟩ :=
    AspisR1.ExtractedMaskTowerBasisExact.current_mul_tower_basis_exact
      q coordinate hq hcoord
  have hzvalue' : AspisR1.ExtractedMaskQM31Exact.decode z =
      AspisR1.ExtractedMaskTowerBasisExact.basisElement (column.val % 4) *
        AspisR1.ExtractedMaskQM31Exact.decode q := by
    simpa [coordinate,
      column_and_three_eq_mod_four column (by omega : column.val < 16)] using hzvalue
  let destination := core.convert.num.FromUsizeU8.from
    (state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.val[column.val]'
      (by simpa [state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS.property] using hcolumn))
  have hdestination : destination.val = (maskExponent j).val := by
    simpa [destination, core.convert.num.FromUsizeU8.from_val_eq] using
      mask_factor_table_cell j
  have hset :
      AspisR1.ExtractedMaskCoefficientLoop1.writeAt1
        maskOnly coefficients column hcolumn = coefficients.set destination z := by
    simp [AspisR1.ExtractedMaskCoefficientLoop1.writeAt1,
      q, coordinate, destination, hmul]
  have hbound : destination.val < 27 := by
    rw [hdestination]
    exact (maskExponent j).isLt
  have hfin : (⟨destination.val, hbound⟩ : Fin 27) = maskExponent j :=
    Fin.ext hdestination
  rw [hset, AspisR1.ExtractedMaskCoefficientDecode.decodedCoefficients_set
    coefficients destination z hbound, hfin, hzvalue']
  simp [j, q, AspisR1.ExtractedMaskCoefficientStep.maskCell]

#print axioms decoded_writeAt0
#print axioms decoded_writeAt1

end AspisR1.ExtractedMaskCoefficientWriteMeaning
