import RPz7_S1ClosedPreparationHashCodeV1
import IndexedCandidateOrdinaryRetainedBridgeV5
set_option autoImplicit false
namespace AspisR1.JGg_OrdinaryTotal
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge
open AspisR1ClaimPreparedBridge

theorem source (block : Array U8 32#usize) :
    ∃ out,AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic block=ok out := by
  obtain ⟨value,call,meaning⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOrdinaryRetainedBridgeV5.ordinary_sample_candidate_eq_fieldRank block
  refine ⟨AspisR1Post25SamplerPreparedCarrier.candidateToPE value,?_⟩
  unfold AspisR1Post25SamplerOrdinaryCallbackV2.candidateOrdinaryPublic
  rw [call,bind_tc_ok]
#print axioms source
end AspisR1.JGg_OrdinaryTotal
