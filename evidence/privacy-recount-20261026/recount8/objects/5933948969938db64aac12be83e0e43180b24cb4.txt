import R1Z.ProverRwSamplerModel
import R1Z.ProverCommitSemanticSampler22

/-! Selected release-lowered QM31 sampler equals the existing semantic
challenge component. This does not identify the block read by the real caller. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSemanticSampler
open Aeneas Aeneas.Std Result
open AspisR1 AspisV8R15.ExactTowerBase AspisV8R19.SqueezeOracleBridge
open ProverRwSamplerModel

def decode (q : NewQM) : QM31Exact :=
  ExtractedCurrentQM31Exact.decode (ExtractedQM31SamplerCarrier.toCurrent (toOld q))

theorem sample_qm31 (block : Array U8 32#usize) (q : NewQM)
    (h : ProverRwSampler.sampler.qm31_sample block = ok q) :
    decode q = R0P.SemSource.qm31Sample (decodeState block) := by
  obtain ⟨q0,h0,_,hv⟩ := ProverRwSamplerModel.sample_total block
  have he : q = q0 := Result.ok.inj (h.symm.trans h0)
  subst q
  calc
    decode q0 = AspisV8R19.SamplerFieldDecode.decode
        (ExtractedQM31SamplerCorrect.coordinates (toOld q0)) := rfl
    _ = AspisV8R19.SamplerFieldDecode.decode
        (SamplerNatModel.qm31Digits (SourceSamplerByteRank.rank block)) :=
      congrArg AspisV8R19.SamplerFieldDecode.decode hv
    _ = _ := ProverCommitSemanticSampler22.model_qm31 block

theorem sample_semChal (block : Array U8 32#usize) (q : NewQM)
    (h : ProverRwSampler.sampler.qm31_sample block = ok q) :
    algebraMap QM31Exact AspisWideTower.WideExact (decode q) =
      R0P.SemSource.semChal (decodeState block) :=
  congrArg (algebraMap QM31Exact AspisWideTower.WideExact) (sample_qm31 block q h)

theorem sample_total_semChal (block : Array U8 32#usize) :
    ∃ q : NewQM, ProverRwSampler.sampler.qm31_sample block = ok q ∧
      algebraMap QM31Exact AspisWideTower.WideExact (decode q) =
        R0P.SemSource.semChal (decodeState block) := by
  obtain ⟨q,hq,_,_⟩ := ProverRwSamplerModel.sample_total block
  exact ⟨q,hq,sample_semChal block q hq⟩

#print axioms sample_qm31
#print axioms sample_semChal
#print axioms sample_total_semChal
end R1Z.ProverRwSemanticSampler
