import NIX_SecureOodLaw
import NIX_FallbackLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIX_SamplerLaw
open Aeneas Aeneas.Std Result
open AspisR1CircleSampleWrapper

def reply (row : r0_transcript.CircleRow)
 (mapped : core.result.Result circle.SecureCirclePoint circle.CirclePointError) : circle.SecureCirclePoint :=
 match mapped with | .Ok p=>p | .Err _=>NIX_FallbackLaw.expected row

/-- The exact native caller G after substituting the two CLOSED callee replies.
Both mapper errors take the SAME row-specific fallback; no retry is introduced. -/
theorem source_of_log (block : Array U8 32#usize) (row : r0_transcript.CircleRow)
 (q : field.QM31) (mapped : core.result.Result circle.SecureCirclePoint circle.CirclePointError)
 (sample : sampler.qm31_sample block=ok q)
 (map : _root_.circle.secure_ood_circle_point_from_parameter q=ok mapped) :
 sampler.circle_sample block row=ok (reply row mapped) := by
 cases mapped with
 | Ok p=>exact RawCircleSampleEmittedWrapperLaw.success_returns_point block row q p sample map
 | Err e=>
   cases row
   · exact RawCircleSampleActualFallbackResultV4.firstFallbackActual block q e sample map
   · exact RawCircleSampleActualFallbackResultV4.secondFallbackActual block q e sample map

/-- Canonical input to the secure mapper is obtained from the SAME sampled block. -/
theorem packet (block : Array U8 32#usize) (row : r0_transcript.CircleRow) :
 ∃ q mapped,
 sampler.qm31_sample block=ok q ∧
 AspisV8R19.SamplerClosureProductCorrectness.Canonical (toR72QM q) ∧
 _root_.circle.secure_ood_circle_point_from_parameter q=ok mapped ∧
 sampler.circle_sample block row=ok (reply row mapped) := by
 obtain ⟨q,sample,domain⟩:=RawCircleSampleActualPolicyUnconditionalV1.sampler_total_canonical block
 let mapped:=NIX_SecureOodLaw.wrapperReply
  (AspisV8R19.SamplerClosureCircleSourceExecution.encodeResult
   (AspisV8R19.SamplerCirclePolicy.pureMap
    (AspisV8R19.SamplerClosureProductCorrectness.decode (toR72QM q))))
 have map : _root_.circle.secure_ood_circle_point_from_parameter q=ok mapped :=
  NIX_SecureOodLaw.wrapper_source q domain
 exact ⟨q,mapped,sample,domain,map,source_of_log block row q mapped sample map⟩

/-- The adopted FinishModel packet consumes the very same block and row. -/
theorem adopted (block : Array U8 32#usize) (row : AspisR1PublicPreparation.FinishModel.CircleRow) :
 ∃ q mapped,
 sampler.qm31_sample block=ok q ∧
 AspisV8R19.SamplerClosureProductCorrectness.Canonical (toR72QM q) ∧
 _root_.circle.secure_ood_circle_point_from_parameter q=ok mapped ∧
 F3M_CircleSource.source block row=ok
  (F3M_CircleSource.point (reply (F3M_CircleSource.row row) mapped)) := by
 obtain ⟨q,mapped,sample,domain,map,run⟩:=packet block (F3M_CircleSource.row row)
 refine ⟨q,mapped,sample,domain,map,?_⟩
 unfold F3M_CircleSource.source
 rw [run]
 rfl

#print axioms source_of_log
#print axioms packet
#print axioms adopted
end AspisR1.NIX_SamplerLaw
end
