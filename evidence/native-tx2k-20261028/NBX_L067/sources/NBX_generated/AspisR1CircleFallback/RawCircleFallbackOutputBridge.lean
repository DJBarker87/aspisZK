import AspisR1CircleFallback.Funs
import AspisV8R19.SamplerClosureCircleSourceExecution
import R0P.CircleSampler

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CircleFallback
namespace RawCircleFallbackOutputBridge

open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerClosureProductExecution (encode)
open AspisV8R19.SamplerCirclePolicy
open R0P.SemSource

private def fallbackParameter0 : field.QM31 :=
  { c0 := field.CM31.ZERO, c1 := field.CM31.ONE }

private def fallbackParameter1 : field.QM31 :=
  { c0 := field.CM31.ONE, c1 := field.CM31.ONE }

theorem parameter0_decodes :
    decode (toR72QM fallbackParameter0) = circleFallbackParameter0 := by
  simp [decode, toR72QM, toR72CM, fallbackParameter0, circleFallbackParameter0,
    field.CM31.ZERO, field.CM31.ONE]
  constructor <;> ext <;> rfl

theorem parameter1_decodes :
    decode (toR72QM fallbackParameter1) = circleFallbackParameter1 := by
  simp [decode, toR72QM, toR72CM, fallbackParameter1, circleFallbackParameter1,
    field.CM31.ZERO, field.CM31.ONE]
  ext <;> rfl

theorem parameter0_canonical : Canonical (toR72QM fallbackParameter0) := by
  norm_num [Canonical, toR72QM, toR72CM, fallbackParameter0,
    field.CM31.ZERO, field.CM31.ONE] <;> rfl

theorem parameter1_canonical : Canonical (toR72QM fallbackParameter1) := by
  norm_num [Canonical, toR72QM, toR72CM, fallbackParameter1,
    field.CM31.ZERO, field.CM31.ONE] <;> rfl

theorem secure_parameter0_output :
    AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
      (toR72QM fallbackParameter0) =
      .ok (.Ok (encodePoint (point circleFallbackParameter0))) := by
  rw [source_execution _ parameter0_canonical, parameter0_decodes,
    outside_map circleFallbackParameter0 circleFallbackParameter0_im]
  rfl

theorem secure_parameter1_output :
    AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
      (toR72QM fallbackParameter1) =
      .ok (.Ok (encodePoint (point circleFallbackParameter1))) := by
  rw [source_execution _ parameter1_canonical, parameter1_decodes,
    outside_map circleFallbackParameter1 circleFallbackParameter1_im]
  rfl

theorem generated_parameter0_output :
    AspisR1CircleFallback.circle.secure_ood_circle_point_from_parameter
      fallbackParameter0 =
      .ok (.Ok (fromR72Point (encodePoint (point circleFallbackParameter0)))) := by
  unfold AspisR1CircleFallback.circle.secure_ood_circle_point_from_parameter
  rw [secure_parameter0_output]
  rfl

theorem generated_parameter1_output :
    AspisR1CircleFallback.circle.secure_ood_circle_point_from_parameter
      fallbackParameter1 =
      .ok (.Ok (fromR72Point (encodePoint (point circleFallbackParameter1)))) := by
  unfold AspisR1CircleFallback.circle.secure_ood_circle_point_from_parameter
  rw [secure_parameter1_output]
  rfl

theorem decode_roundtrip_generated (q : QM31Exact) :
    decode (toR72QM (fromR72QM (encode q))) = q := by
  simp only [toR72QM, fromR72QM, toR72CM, fromR72CM]
  exact decode_encode q

private theorem fallback_mod0 : (0#usize % 2#usize) = ok 0#usize := by
  rfl

private theorem fallback_mod1 : (1#usize % 2#usize) = ok 1#usize := by
  rfl

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i =
      .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem fallback_entry0 :
    Array.index_usize transcript.CIRCLE_FALLBACK_PARAMETERS 0#usize =
      .ok fallbackParameter0 := by
  rw [array_index_usize_ok _ _ (by decide)]
  simp [transcript.CIRCLE_FALLBACK_PARAMETERS, Array.make, fallbackParameter0,
    field.CM31.ZERO, field.CM31.ONE]

private theorem fallback_entry1 :
    Array.index_usize transcript.CIRCLE_FALLBACK_PARAMETERS 1#usize =
      .ok fallbackParameter1 := by
  rw [array_index_usize_ok _ _ (by decide)]
  simp [transcript.CIRCLE_FALLBACK_PARAMETERS, Array.make, fallbackParameter1,
    field.CM31.ZERO, field.CM31.ONE]

theorem fallback_zero_output :
    transcript.circle_fallback_point 0#usize =
      .ok (fromR72Point (encodePoint (point circleFallbackParameter0))) := by
  unfold transcript.circle_fallback_point
  rw [fallback_mod0]
  simp only [bind_tc_ok, fallback_entry0, generated_parameter0_output]

theorem fallback_one_output :
    transcript.circle_fallback_point 1#usize =
      .ok (fromR72Point (encodePoint (point circleFallbackParameter1))) := by
  unfold transcript.circle_fallback_point
  rw [fallback_mod1]
  simp only [bind_tc_ok, fallback_entry1, generated_parameter1_output]

/-- The decoded coordinates of the extracted fallback output agree with the
coordinates of the retained R0P fallback point. The latter's point-on-circle
proof is already part of `circleFallback0`. -/
theorem fallback_zero_coordinates_match :
    (algebraMap QM31Exact AspisWideTower.WideExact
        (decode (toR72QM (fromR72Point (encodePoint (point circleFallbackParameter0))).x)),
      algebraMap QM31Exact AspisWideTower.WideExact
        (decode (toR72QM (fromR72Point (encodePoint (point circleFallbackParameter0))).y))) =
      circleFallback0.1 := by
  simp only [encodePoint, fromR72Point, decode_roundtrip_generated,
    circleFallback0, embedCirclePoint]

theorem fallback_one_coordinates_match :
    (algebraMap QM31Exact AspisWideTower.WideExact
        (decode (toR72QM (fromR72Point (encodePoint (point circleFallbackParameter1))).x)),
      algebraMap QM31Exact AspisWideTower.WideExact
        (decode (toR72QM (fromR72Point (encodePoint (point circleFallbackParameter1))).y))) =
      circleFallback1.1 := by
  simp only [encodePoint, fromR72Point, decode_roundtrip_generated,
    circleFallback1, embedCirclePoint]

#print axioms parameter0_canonical
#print axioms parameter1_canonical
#print axioms secure_parameter0_output
#print axioms secure_parameter1_output
#print axioms generated_parameter0_output
#print axioms generated_parameter1_output
#print axioms fallback_zero_output
#print axioms fallback_one_output
#print axioms fallback_zero_coordinates_match
#print axioms fallback_one_coordinates_match

end RawCircleFallbackOutputBridge
end AspisR1CircleFallback
