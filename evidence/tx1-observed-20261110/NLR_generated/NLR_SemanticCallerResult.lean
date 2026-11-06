import NLR_ConvertedReply
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_SemanticCallerResult
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (run)
/-- Derive the source success of the SAME137 call from its COMPLETE packet
and the entered success branch. No successful child is a root premise. -/
theorem source (native : NLR_Interface.Native137) (child137 : NLR_Interface.RowSpec_137 native)
 (reservation : NP6_StdModel.Reservation) (i : NLJ_Prepare.Input Unit)
 (v : verifier.View) (before : NLR_Interface.ExternalFrame) (domain : v.semantic.val.length=13831)
 (sem : r1_semantic.Verified Unit)
 (returned : NLR_PrepareSemantic137.reply
  (native (NLR_PrepareSemantic137.observedInput reservation i v) before).reply=ok (.Ok sem)) :
 let call := NLR_PrepareSemantic137.observedInput reservation i v
 (run (S1SemanticCode.verify (S1SemanticCode.finish NJM_RoundJoin.R
  (IDa_Deployed.boundaries reservation)) call.digest call.publicValue call.bytes call.hash none)).2 =
 ok (.Ok ((S1SemanticCarrier.semanticEquiv Unit).symm sem)) := by
 have actual := congrArg Prod.snd
  (child137 (NLR_PrepareSemantic137.observedInput reservation i v) before domain).2.2.2
 exact actual.trans (NLR_ConvertedReply.success _ sem returned)
#print axioms source
set_option pp.proofs false
#print source
end AspisR1.NLR_SemanticCallerResult
end
