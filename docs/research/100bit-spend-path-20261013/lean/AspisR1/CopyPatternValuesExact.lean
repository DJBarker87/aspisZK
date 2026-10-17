import AspisR1.CopyPatternSource
import AspisR1.CopyPatternOuterExact
import AspisR1.CopyPatternPowersExact
import AspisR1.ArrayZeroExact

/-! Entire actual Copy pattern generator equals the retained same-input model. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternValuesExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ArrayUpdateCanonicalExact (CanonicalArray cells)
open AspisR1.ArrayZeroExact
open AspisR1.CopyPatternLimbExact

theorem literal_patterns_success (openings : Array QM 16#usize) (lambda : QM)
    (hopenings : CanonicalArray openings)
    (hlambda : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM lambda) :
    ∃ out,
      AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal
        openings lambda = .ok out ∧
      CanonicalArray out ∧ decodedCells out =
        R0P.copyPatternValuesLiteral (decodedCells openings) (decode lambda) := by
  obtain ⟨powers,hpowersRun,hpowers,hpowersModel⟩ :=
    AspisR1.CopyPatternPowersExact.initialized_powers_exact lambda hlambda
  obtain ⟨out,houter,hcout,hout⟩ :=
    AspisR1.CopyPatternOuterExact.patterns_outer_success_fuel openings powers
      (decode lambda) 16#usize (Array.repeat 14#usize field.QM31.ZERO) 0#usize 14
      (by scalar_tac) hopenings hpowers hpowersModel repeat_zero_canonical
      (by intro j hj; simp only [UScalar.ofNatCore_val_eq] at hj; omega)
  refine ⟨out,?_,hcout,?_⟩
  · simp only [AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values_literal,
      hpowersRun,houter,bind_tc_ok]
  · funext j
    change decode (cells out j) = _
    exact hout j

theorem patterns_success (openings : Array QM 16#usize) (lambda : QM)
    (hopenings : CanonicalArray openings)
    (hlambda : AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM lambda) :
    ∃ out,
      AspisR1CopyPatternCandidate.pool_v1.pair_forest_copy_terminal.pattern_values
        openings lambda = .ok out ∧
      CanonicalArray out ∧ decodedCells out =
        R0P.copyPatternValuesLiteral (decodedCells openings) (decode lambda) := by
  exact literal_patterns_success openings lambda hopenings hlambda

#print axioms literal_patterns_success
#print axioms patterns_success
end
end AspisR1.CopyPatternValuesExact
