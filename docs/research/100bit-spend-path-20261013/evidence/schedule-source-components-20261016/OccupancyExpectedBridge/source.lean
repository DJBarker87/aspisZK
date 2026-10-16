import OccupancyGeneratedSlice
import R0P.Occupancy
import ExtractedMaskConstants
import ExtractedMaskQM31Exact

/-! Source-checked variant output and the exact QM31 lift used by the
occupancy literal lane 11. -/
set_option autoImplicit false
namespace AspisR1.OccupancyExpectedBridge

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev ExactQM := QM31Exact

def modelVariant : pool_v1.pair_forest_semantic_terminal.CompiledVariant → R0P.Variant
  | .PrivateTransfer => .privateTransfer
  | .Withdrawal => .withdrawal

theorem variant_expected_lift_exact
    (v : pool_v1.pair_forest_semantic_terminal.CompiledVariant) :
    ∃ m : field.M31, ∃ q : QM,
      pool_v1.pair_forest_semantic_terminal.variant_expected_output v = .ok m ∧
      pool_v1.pair_forest_semantic_terminal.lift_m31 m = .ok q ∧
      Canonical q ∧
      decode q = R0P.occupancyExpected (modelVariant v) := by
  cases v with
  | PrivateTransfer =>
      refine ⟨1#u32, field.QM31.ONE, ?_, ?_, ?_, ?_⟩
      · simp [pool_v1.pair_forest_semantic_terminal.variant_expected_output]
      · simp [pool_v1.pair_forest_semantic_terminal.lift_m31,
          field.CM31.from_m31, field.QM31.from_cm31,
          field.M31.ZERO, field.CM31.ZERO, field.QM31.ONE]
      · exact AspisR1.ExtractedMaskConstants.one_canonical
      · simpa [modelVariant, R0P.occupancyExpected] using
          AspisR1.ExtractedMaskConstants.one_decode
  | Withdrawal =>
      refine ⟨0#u32, field.QM31.ZERO, ?_, ?_, ?_, ?_⟩
      · simp [pool_v1.pair_forest_semantic_terminal.variant_expected_output]
      · simp [pool_v1.pair_forest_semantic_terminal.lift_m31,
          field.CM31.from_m31, field.QM31.from_cm31,
          field.M31.ZERO, field.CM31.ZERO, field.QM31.ZERO]
      · exact AspisR1.ExtractedMaskConstants.zero_canonical
      · simpa [modelVariant, R0P.occupancyExpected] using
          AspisR1.ExtractedMaskConstants.zero_decode

#print axioms variant_expected_lift_exact
end AspisR1.OccupancyExpectedBridge
