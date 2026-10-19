import AspisR1CircleSampleWrapper.RawCircleSampleActualPolicyUnconditionalV1
import AspisR1CircleSampleWrapper.Funs
import ExtractedSourceSemanticSampler

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CircleSampleWrapper
namespace RawCircleSampleActualModelV4

open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SqueezeOracleBridge
open AspisR1PublicPreparation.SamplerTransport
open AspisR1PublicPreparation.SourceSemanticSampler

/-- The exact R72-decoded parameter used by the actual wrapper is the
    selected semantic one-block sampler output for the same 32-byte block. -/
theorem actual_sample_parameter_eq_model
    (block : Array Std.U8 32#usize) (q : AspisR1CircleSampleWrapper.field.QM31)
    (h : _root_.sampler.qm31_sample block = .ok q) :
    decode (toR72QM q) = R0P.SemSource.qm31Sample (decodeState block) := by
  have hwrap := RawCircleSampleEmittedWrapperLaw.sampler_qm31_sample_eq_public block
  cases hp : AspisR1PublicPreparation.sampler.qm31_sample block with
  | ok qp =>
      have hq : q = fromPublicQM qp := by
        apply Result.ok.inj
        calc
          .ok q = _root_.sampler.qm31_sample block := h.symm
          _ = (do
            let q ← AspisR1PublicPreparation.sampler.qm31_sample block
            ok (fromPublicQM q)) := hwrap
          _ = .ok (fromPublicQM qp) := by simp [hp]
      subst q
      change AspisV8R19.SamplerClosureProductCorrectness.decode
          (_root_.toR72QM (fromPublicQM qp)) = _
      have hm := AspisR1PublicPreparation.SourceSemanticSampler.sample_qm31 block qp hp
      have hdecode : decode (_root_.toR72QM (_root_.fromPublicQM qp)) =
          AspisR1.ExtractedCurrentQM31Exact.decode
            (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
              (AspisR1PublicPreparation.SamplerTransport.toOld qp)) := by
        cases qp with
        | mk c0 c1 =>
          cases c0 with
          | mk a0 a1 =>
            cases c1 with
            | mk a2 a3 => rfl
      exact hdecode.trans hm
  | fail e =>
      simp [hwrap, hp] at h
  | div =>
      simp [hwrap, hp] at h

#print axioms actual_sample_parameter_eq_model

end RawCircleSampleActualModelV4
end AspisR1CircleSampleWrapper
