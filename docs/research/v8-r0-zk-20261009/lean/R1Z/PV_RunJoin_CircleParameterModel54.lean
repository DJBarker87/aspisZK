import R1Z.PV_RunJoin_PublicSampler54
import R1Z.PV_RunJoin_SamplerCanonical54
import R1Z.ProverCommitCircleSampler22
import R1Z.PV_RunJoin_CircleR72Carrier52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleParameterModel54
abbrev Q := (U32 × U32) × (U32 × U32)
def wrapper (q : Q) : AspisR1CircleSampleWrapper.field.QM31 :=
  ⟨⟨q.1.1,q.1.2⟩,⟨q.2.1,q.2.2⟩⟩
def value (q : Q) := AspisV8R19.SamplerClosureProductCorrectness.decode
  (PV_RunJoin_CircleR72Carrier52.encQ q)

theorem complete (block : Array U8 32#usize) :
    ∃ q, PV_RunJoin_CircleRawSampler52.shipped_sampler.qm31_sample block=ok q ∧
      PV_RunJoin_CircleNeutralShape53.QC q ∧ value q=
        R0P.SemSource.qm31Sample (AspisV8R19.SqueezeOracleBridge.decodeState block) := by
  obtain ⟨q,hq,hc⟩ := PV_RunJoin_SamplerCanonical54.complete block
  have hpublic : AspisR1PublicPreparation.sampler.qm31_sample block=ok (PV_RunJoin_PublicSampler54.encode q) := by
    rw [PV_RunJoin_PublicSampler54.complete,hq,bind_tc_ok]
  have sampled : _root_.sampler.qm31_sample block=ok (wrapper q) := by
    rw [AspisR1CircleSampleWrapper.RawCircleSampleEmittedWrapperLaw.sampler_qm31_sample_eq_public,
      hpublic,bind_tc_ok]
    rfl
  have meaning := ProverCommitCircleSampler22.parameter_eq block (wrapper q) sampled
  exact ⟨q,hq,hc,meaning⟩
#print axioms wrapper
#print axioms value
#print axioms complete
end R1Z.PV_RunJoin_CircleParameterModel54
