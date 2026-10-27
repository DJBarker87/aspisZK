import ExtractedMaskCoefficientStep
import ExtractedMaskQM31Exact

/-! Draft only: transport one actual Aeneas `Array.set` coefficient write to
its decoded finite-field coefficient function. No canonicality is needed. -/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskCoefficientDecode

open Aeneas Aeneas.Std

abbrev QM := AspisR1.ExtractedMaskCoefficientStep.QM
abbrev Coefficients := AspisR1.ExtractedMaskCoefficientStep.Coefficients
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact

def decodedCoefficients (a : Coefficients) : Fin 27 → ExactQM :=
  fun i => AspisR1.ExtractedMaskQM31Exact.decode
    (AspisR1.ExtractedMaskCoefficientStep.coefficientCell a i)

/-- An in-bounds write to the actual 27-cell coefficient array decodes to the
corresponding functional `Function.update`. The destination is represented by
its `Fin 27` value, with its bound supplied explicitly. -/
theorem decodedCoefficients_set
    (a : Coefficients) (destination : Usize) (transformed : QM)
    (hbound : destination.val < 27) :
    decodedCoefficients (a.set destination transformed) =
      Function.update (decodedCoefficients a)
        ⟨destination.val, hbound⟩
        (AspisR1.ExtractedMaskQM31Exact.decode transformed) := by
  funext j
  have hj : j.val < (a.set destination transformed).length := by
    simpa using j.isLt
  by_cases heq : destination.val = j.val
  · have hcell :=
      Array.getElem_Nat_set_eq a destination j.val transformed hj heq
    have hfin : (⟨destination.val, hbound⟩ : Fin 27) = j := Fin.ext heq
    change AspisR1.ExtractedMaskQM31Exact.decode
      ((a.set destination transformed)[j.val]) = _
    rw [hcell]
    simp [hfin]
  · have hcell :=
      Array.getElem_Nat_set_ne a destination j.val transformed hj heq
    have hfin : (⟨destination.val, hbound⟩ : Fin 27) ≠ j := by
      intro h
      exact heq (congrArg Fin.val h)
    change AspisR1.ExtractedMaskQM31Exact.decode
      ((a.set destination transformed)[j.val]) = _
    rw [hcell]
    rw [Function.update_of_ne (Ne.symm hfin)]
    rfl

#print axioms decodedCoefficients_set

end AspisR1.ExtractedMaskCoefficientDecode
