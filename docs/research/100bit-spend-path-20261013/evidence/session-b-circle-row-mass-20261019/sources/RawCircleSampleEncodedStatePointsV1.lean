import RawCircleSampleEncodedStateRowsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleEncodedStatePointsV1

open RawCircleSampleEncodedStateRowsV1
open RawCircleSamplePointwiseModelV1
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.SourceDuplexStep
open AspisR0.ChordGeometry
open R0P.SemSource

/-- Reify the extracted wrapper coordinates as the corresponding model point.
    Its circle proof is transported from the model point using the coordinate
    agreement theorem, so this adapter introduces no new circle assumption. -/
def toModelPoint (p : circle.SecureCirclePoint)
    (row : r0_transcript.CircleRow) (s : State)
    (hcoords : actualWideCoordinates p = (modelPoint row s).val) :
    Point AspisWideTower.WideExact :=
  ⟨actualWideCoordinates p, by rw [hcoords]; exact (modelPoint row s).property⟩

/-- The actual row-25 wrapper output, reified as the same point used by the
    semantic model. Row 25 is the first circle row (`CircleRow.First`). -/
theorem actual_row25_point_eq_model (s : State) :
    ∃ p : circle.SecureCirclePoint,
      ∃ hcoords : actualWideCoordinates p = (circleSample0 s).val,
        sampler.circle_sample (encodeState s) .First = .ok p ∧
        toModelPoint p .First s hcoords = circleSample0 s := by
  obtain ⟨p, hout, _hcircle⟩ :=
    RawCircleSampleActualPolicyUnconditionalV1.circle_sample_total_on_circle
      (encodeState s) .First
  obtain ⟨p', hout', hcoords'⟩ := actual_row25_output_matches_model s
  have hpeq : p = p' := Result.ok.inj (hout.symm.trans hout')
  subst p'
  refine ⟨p, ?_, hout, ?_⟩
  · change actualWideCoordinates p = (circleSample0 s).val
    exact hcoords'
  · apply Subtype.ext
    change actualWideCoordinates p = (circleSample0 s).val
    exact hcoords'

/-- The actual row-26 wrapper output, reified as the same point used by the
    semantic model. Row 26 is the second circle row (`CircleRow.Second`). -/
theorem actual_row26_point_eq_model (s : State) :
    ∃ p : circle.SecureCirclePoint,
      ∃ hcoords : actualWideCoordinates p = (circleSample1 s).val,
        sampler.circle_sample (encodeState s) .Second = .ok p ∧
        toModelPoint p .Second s hcoords = circleSample1 s := by
  obtain ⟨p, hout, _hcircle⟩ :=
    RawCircleSampleActualPolicyUnconditionalV1.circle_sample_total_on_circle
      (encodeState s) .Second
  obtain ⟨p', hout', hcoords'⟩ := actual_row26_output_matches_model s
  have hpeq : p = p' := Result.ok.inj (hout.symm.trans hout')
  subst p'
  refine ⟨p, ?_, hout, ?_⟩
  · change actualWideCoordinates p = (circleSample1 s).val
    exact hcoords'
  · apply Subtype.ext
    change actualWideCoordinates p = (circleSample1 s).val
    exact hcoords'

#print axioms toModelPoint
#print axioms actual_row25_point_eq_model
#print axioms actual_row26_point_eq_model

end RawCircleSampleEncodedStatePointsV1
end AspisR1CircleSampleWrapper
