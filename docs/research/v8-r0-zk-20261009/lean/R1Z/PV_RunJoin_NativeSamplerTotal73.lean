import R1Z.PV_RunJoin_NativeResidual63
import R1Z.PV_RunJoin_SemanticSamplerField51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSamplerTotal73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F) (block : Array U8 32#usize) :
    ∃ q, @ProverRwFull.sampler.qm31_sample (types base) (opsNative base heap box ops runtime world) block=ok q := by
  obtain ⟨q,hq,hcanonical,hcoordinates⟩ := AspisR1.ExtractedQM31SamplerCorrect.sample_total block
  refine ⟨ProverRwFullSampler.fromSelected (ProverRwSamplerModel.fromOld q),?_⟩
  change (opsNative base heap box ops runtime world).op248 _=_
  rw [PV_RunJoin_SemanticSamplerField51.installed
    (PV_RunJoin_NativeResidual62.baseTypes base) heap box (residual base ops runtime world)]
  unfold ProverRwFullSampler.selected
  rw [ProverRwSamplerModel.sample_exact,hq]
  rfl

#print axioms complete
end R1Z.PV_RunJoin_NativeSamplerTotal73
