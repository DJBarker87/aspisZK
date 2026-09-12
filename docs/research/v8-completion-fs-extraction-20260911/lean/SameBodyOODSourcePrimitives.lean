import SameBodyOODData
import SameBodyOrdinary
import FSLiveOODV7Decode

/-!
# OOD source primitives

Two deterministic prerequisites for the chronological OOD-data bridge:

* every point returned by the concrete V7 decoder has canonically decodable
  exact coordinates; and
* the body-field answer-row projection is definitionally the ordinary
  verifier's OOD projection.

The enclosing successful source execution still has to expose the successful
decoder calls for its two returned points.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000

namespace AspisV8Completion.SameBodyOODSourcePrimitives

open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73SecureCircleMap
open FSV7OODSampler FSLiveOODV7Decode
open AspisV8.SameBodySequentialCodec
open SameBodyOODData

abbrev K := QM31Exact
abbrev Point := SecureCirclePointBytes

noncomputable section

theorem exact_point_coordinates (parameter : K) (point : Point)
    (success : exactSecureCirclePointFromDecoded parameter = some point) :
    ∃ x y : K,
      decodeTagQM31ExactLE point.x = some x ∧
      decodeTagQM31ExactLE point.y = some y := by
  let square := qm31Square parameter
  let denominator := (1 : K) + square
  by_cases inSubfield : parameter.im = 0
  · cases inverseEq : qm31TryInv denominator <;>
      simp [exactSecureCirclePointFromDecoded, square, denominator,
        inverseEq, inSubfield] at success
  · cases inverseEq : qm31TryInv denominator with
    | none =>
        simp [exactSecureCirclePointFromDecoded, square, denominator,
          inverseEq] at success
    | some inverse =>
        have pointEq : point =
            encodeExactSecureCirclePoint parameter square inverse := by
          simpa [exactSecureCirclePointFromDecoded, square, denominator,
            inverseEq, inSubfield] using success.symm
        subst point
        exact ⟨_, _, decode_encodeExactSecureCirclePoint_x _ _ _,
          decode_encodeExactSecureCirclePoint_y _ _ _⟩

theorem decodePoint_coordinates (limbs : List Nat) (point : Point)
    (success : decodePoint limbs = some point) :
    ∃ x y : K,
      decodeTagQM31ExactLE point.x = some x ∧
      decodeTagQM31ExactLE point.y = some y := by
  unfold decodePoint at success
  cases assembled : assemble limbs with
  | none => simp [assembled] at success
  | some parameter =>
      simp only [assembled, Option.bind_some] at success
      exact exact_point_coordinates parameter point success

theorem successfulCircle_coordinates (point : Point)
    (attempts : List CircleAttempt) (success : SuccessfulCircle point attempts) :
    ∃ x y : K,
      decodeTagQM31ExactLE point.x = some x ∧
      decodeTagQM31ExactLE point.y = some y := by
  induction success with
  | final attempt values sampled decoded =>
      exact decodePoint_coordinates values point decoded
  | retry attempt values rest sampled rejected tail ih => exact ih

theorem successfulDistinct_coordinates (excluded point : Point)
    (tape : FSLiveOODV7Decode.Tape)
    {start final : FSLiveOODV7Decode.Transcript}
    {rounds : List CircleTrace}
    (chronological : ChronologicalDistinct tape start rounds final)
    (success : SuccessfulDistinct excluded point rounds) :
    ∃ x y : K,
      decodeTagQM31ExactLE point.x = some x ∧
      decodeTagQM31ExactLE point.y = some y := by
  induction chronological with
  | nil current => cases success
  | cons current round rest final actual tail ih =>
      subst round
      cases success with
      | final round accepted different =>
          exact successfulCircle_coordinates point _
            (circleTrace_successful tape 3 current point accepted)
      | retry round remaining equal successfulTail =>
          exact ih successfulTail

/-- The source and ordinary-relation definitions use the same field-number
formula.  This proves the mathematical index alignment; literal Rust parser
refinement remains separate. -/
theorem answerIndex_eq_oodIndex (sample : Fin 2) (lane : Fin 29) :
    answerIndex sample lane =
      (SameBodyOrdinary.oodIndex sample lane).val := by
  rfl

theorem answerRows_eq_ordinaryOOD (values : List K)
    (sample : Fin 2) (lane : Fin 29) :
    answerRows values sample lane =
      SameBodyOrdinary.ood (fun i => values.getD i.val 0) sample lane := by
  rfl

#print axioms exact_point_coordinates
#print axioms decodePoint_coordinates
#print axioms successfulCircle_coordinates
#print axioms successfulDistinct_coordinates
#print axioms answerIndex_eq_oodIndex
#print axioms answerRows_eq_ordinaryOOD

end
end AspisV8Completion.SameBodyOODSourcePrimitives
