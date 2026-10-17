import AspisR1.CopyPatternLoopFuel
import AspisR1.CopyPatternRegistryModel
import ExtractedMaskConstants

/-! Each actual fixed-table pattern compression is the retained same-input formula. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternSingleExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.CopyPatternLimbExact AspisR1.CopyPatternLoopFactor
open AspisR1.CopyPatternLoopFuel AspisR1.CopyPatternRegistryModel
open AspisR1.CopyPatternFoldModel

theorem pattern_source_exact (openings powers : Array QM 16#usize)
    (lambda : ExactQM) (index : Fin 14)
    (hopenings : AspisR1.ArrayUpdateCanonicalExact.CanonicalArray openings)
    (hpowers : AspisR1.ArrayUpdateCanonicalExact.CanonicalArray powers)
    (hpowersModel : decodedCells powers = R0P.copyPowers lambda) :
    ∃ out, Loop openings powers 0#usize (rawAt index) field.QM31.ZERO =
        .ok (16#usize,out) ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM out ∧
      decode out = R0P.copyPatternValuesLiteral (decodedCells openings) lambda index := by
  obtain ⟨out,hrun,hcanonical,hvalue⟩ := pattern_loop_success_fuel
    openings powers 0#usize (rawAt index) field.QM31.ZERO 16 (by scalar_tac)
    (raw_columns index) (raw_offsets index) hopenings hpowers
    AspisR1.ExtractedMaskConstants.zero_canonical
  refine ⟨out,hrun,hcanonical,?_⟩
  simpa only [UScalar.ofNatCore_val_eq,raw_model,hpowersModel,
    AspisR1.ExtractedMaskConstants.zero_decode,remaining_zero] using hvalue

#print axioms pattern_source_exact
end
end AspisR1.CopyPatternSingleExact
