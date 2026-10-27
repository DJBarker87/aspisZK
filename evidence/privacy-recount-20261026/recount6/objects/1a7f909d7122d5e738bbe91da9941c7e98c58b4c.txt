import AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1
import AspisR1CircleSampleWrapper.RawCircleSampleActualFallbackCoordinatesV1
import R1Z.ProverCommitSemanticSampler22

/-! Exact circle coordinates, including both fallbacks, for the retained
extracted wrapper. Current caller/source pinning is a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCircleSampler22
open Aeneas Aeneas.Std Result AspisR1CircleSampleWrapper
open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerCirclePolicy
open R0P.SemSource

def coordinates (p : circle.SecureCirclePoint) : AspisWideTower.WideExact × AspisWideTower.WideExact :=
  (algebraMap QM31Exact AspisWideTower.WideExact (decode (toR72QM p.x)),
   algebraMap QM31Exact AspisWideTower.WideExact (decode (toR72QM p.y)))

def model (block : Array U8 32#usize) (row : r0_transcript.CircleRow) :=
  match row with
  | .First => circleSample0 (AspisV8R19.SqueezeOracleBridge.decodeState block)
  | .Second => circleSample1 (AspisV8R19.SqueezeOracleBridge.decodeState block)

theorem parameter_eq (block : Array U8 32#usize) (q : field.QM31)
    (hq : sampler.qm31_sample block = ok q) :
    decode (toR72QM q) = qm31Sample (AspisV8R19.SqueezeOracleBridge.decodeState block) := by
  obtain ⟨pub, hpub, _, _⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total block
  have hw := RawCircleSampleEmittedWrapperLaw.sampler_qm31_sample_eq_public block
  rw [hpub] at hw
  have he : fromPublicQM pub = q := Result.ok.inj (hw.symm.trans hq)
  rw [← he]
  exact R1Z.ProverCommitSemanticSampler22.sample_qm31 block pub hpub

theorem encoded_coordinates (t : QM31Exact × QM31Exact) :
    coordinates (fromR72Point (encodePoint t)) =
      (algebraMap QM31Exact AspisWideTower.WideExact t.1,
       algebraMap QM31Exact AspisWideTower.WideExact t.2) := by
  change (algebraMap QM31Exact AspisWideTower.WideExact (decode (AspisV8R19.SamplerClosureProductExecution.encode t.1)),
    algebraMap QM31Exact AspisWideTower.WideExact (decode (AspisV8R19.SamplerClosureProductExecution.encode t.2))) = _
  rw [decode_encode, decode_encode]

/-- No success or regular-parameter premise: all blocks and both fallback
rows return exactly the selected model point's two coordinates. -/
theorem circle_total_coordinates (block : Array U8 32#usize) (row : r0_transcript.CircleRow) :
    ∃ p : circle.SecureCirclePoint,
      sampler.circle_sample block row = ok p ∧ coordinates p = (model block row).1 := by
  obtain ⟨q, hq, hc⟩ := RawCircleSampleActualPolicyUnconditionalV1.sampler_total_canonical block
  have hp := parameter_eq block q hq
  have hs := source_execution (toR72QM q) hc
  by_cases hi : (decode (toR72QM q)).im ≠ 0
  · rw [outside_map _ hi] at hs
    have hm : circle.secure_ood_circle_point_from_parameter q =
        ok (.Ok (fromR72Point (encodePoint (point (decode (toR72QM q)))))) := by
      rw [RawCircleSampleEmittedWrapperLaw.secure_circle_eq_r72, hs]
      rfl
    refine ⟨_, RawCircleSampleEmittedWrapperLaw.success_returns_point block row q _ hq hm, ?_⟩
    rw [encoded_coordinates, hp]
    have him : (qm31Sample (AspisV8R19.SqueezeOracleBridge.decodeState block)).im ≠ 0 := hp ▸ hi
    cases row <;>
      simp only [model, circleSample0, circleSample1, circleSampleParameter0,
        circleSampleParameter1, circleSampleParameterWith_accepted _ _ him, embedCirclePoint]
  · have hz : (decode (toR72QM q)).im = 0 := not_ne_iff.mp hi
    obtain ⟨e, he⟩ : ∃ e, pureMap (decode (toR72QM q)) = .error e := by
      by_cases hd : 1 + (decode (toR72QM q))^2 = 0
      · exact ⟨.singular, singular_first _ hd⟩
      · exact ⟨.subfield, by simp [pureMap, hd, hz]⟩
    rw [he] at hs
    have hm : circle.secure_ood_circle_point_from_parameter q =
        ok (.Err (fromR72Error (encodeError e))) := by
      rw [RawCircleSampleEmittedWrapperLaw.secure_circle_eq_r72, hs]
      rfl
    have him : (qm31Sample (AspisV8R19.SqueezeOracleBridge.decodeState block)).im = 0 := hp ▸ hz
    cases row with
    | First =>
      refine ⟨_, RawCircleSampleActualFallbackResultV4.firstFallbackActual block q _ hq hm, ?_⟩
      change coordinates _ = (circleSampleParameterWith circleFallback0 _).1
      rw [circleSampleParameterWith_rejected _ _ him]
      exact RawCircleSampleActualFallbackCoordinatesV1.firstFallbackCoordinates
    | Second =>
      refine ⟨_, RawCircleSampleActualFallbackResultV4.secondFallbackActual block q _ hq hm, ?_⟩
      change coordinates _ = (circleSampleParameterWith circleFallback1 _).1
      rw [circleSampleParameterWith_rejected _ _ him]
      exact RawCircleSampleActualFallbackCoordinatesV1.secondFallbackCoordinates

#print axioms parameter_eq
#print axioms encoded_coordinates
#print axioms circle_total_coordinates
end R1Z.ProverCommitCircleSampler22
end
