import NLR_SemanticCallerResult
import NLR_FinishModelDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_SemanticFinishCaller
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Derive SAME semantic_finish inputs from the087→137 entered success
branch. Value/source packet ONLY; no full136/137 resource packet is assumed
proved. The179 allocation/claims specialization and remaining clauses are not
silently added. -/
theorem reached (native : NLR_Interface.Native137)
 (child137 : NLR_Interface.RowSpec_137 native) (reservation : NP6_StdModel.Reservation)
 (i : NLJ_Prepare.Input Unit) (v : verifier.View) (before : NLR_Interface.ExternalFrame)
 (domain : v.semantic.val.length=13831) (sem : r1_semantic.Verified Unit)
 (returned : NLR_PrepareSemantic137.reply
  (native (NLR_PrepareSemantic137.observedInput reservation i v) before).reply=ok (.Ok sem)) :
 let call := NLR_PrepareSemantic137.observedInput reservation i v
 ∃ (p : AspisR1PublicPreparation.r1_wire.Prefix)
   (initial after : AspisR1PublicPreparation.r1_wire.SemanticTranscript Unit)
   (c : AspisR1PublicPreparation.r1_wire.Challenges),
 AspisR1PublicPreparation.PrefixAdapter.parseAccepted call.bytes=ok (.Ok p) ∧
 (AspisR1PublicPreparation.PreparedHashCode.run
  (AspisR1PublicPreparation.S1SemanticCode.publicTranscript call.digest call.publicValue call.hash p.c1_root)).2=ok (.Ok initial) ∧
 (AspisR1PublicPreparation.PreparedHashCode.run
  (AspisR1PublicPreparation.S1SemanticCode.begin call.digest p initial)).2=ok (.Ok c,after) ∧
 AspisR1PublicPreparation.FinishModel.finish NJM_RoundJoin.R (IDa_Deployed.boundaries reservation)
  call.digest call.publicValue p after c none=ok (.Ok ((S1SemanticCarrier.semanticEquiv Unit).symm sem)) := by
 let call := NLR_PrepareSemantic137.observedInput reservation i v
 exact NLR_FinishModelDomain.reached NJM_RoundJoin.R (IDa_Deployed.boundaries reservation)
  call.digest call.publicValue call.bytes call.hash ((S1SemanticCarrier.semanticEquiv Unit).symm sem)
  (NLR_SemanticCallerResult.source native child137 reservation i v before domain sem returned)
#print axioms reached
set_option pp.proofs false
#print reached
end AspisR1.NLR_SemanticFinishCaller
end
