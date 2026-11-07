import NMC_Transcription
import NLU_FrontierSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMO_Transcription
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- Reviewed frozen source r1_semantic.rs:232-308. This establishes only the
model side of (bl); it makes no assertion about a native invocation. -/
theorem source {H : Type} (input : NLC_Finish.Input H) :
 NLC_Goals.FinishSourceEquality input := NMC_Transcription.source input
/-- The chronological digest projection includes rejected and stopped
prefixes. Resource-only cleanup is absent from this projection under (bl)(3).
No independently chosen endpoint or successful child is a premise. -/
theorem full_outcome {H : Type} (input : NLU.Input H) :
 (NLU.digestLog (NLU_Frontier.run (NLC_Finish.fuel (NLC_Finish.initial input)) (NLU.initial input)).summary.events,
 NLU.eraseReply (NLU_Frontier.run (NLC_Finish.fuel (NLC_Finish.initial input)) (NLU.initial input)).summary.reply)=
 PreparedHashCode.run (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries input.reservation)
 input.digest input.publicValue input.prefix1 input.transcript input.challenges none) :=
 NLU_Frontier.source input
#print axioms source
#print axioms full_outcome
set_option pp.proofs false in #print source
set_option pp.proofs false in #print full_outcome
end AspisR1.NMO_Transcription
end
