import NLR_SemanticFinishCaller
import NLR_FinishReservation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PreparedSemanticClause
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- Discharge179's semantic_finish VALUE clause at the SAME current semantic
object through the canonical equivalence. No full179 domain/native call,
full136 packet or actual allocator success is inferred. -/
theorem source (native : NLR_Interface.Native137)
 (child137 : NLR_Interface.RowSpec_137 native) (reservation : NP6_StdModel.Reservation)
 (i : NLJ_Prepare.Input Unit) (v : verifier.View) (frame : NLR_Interface.ExternalFrame)
 (domain : v.semantic.val.length=13831) (sem : r1_semantic.Verified Unit)
 (returned : NLR_PrepareSemantic137.reply
  (native (NLR_PrepareSemantic137.observedInput reservation i v) frame).reply=ok (.Ok sem)) :
 let call := NLR_PrepareSemantic137.observedInput reservation i v
 ∃ (p : AspisR1PublicPreparation.r1_wire.Prefix)
   (before : AspisR1PublicPreparation.r1_wire.SemanticTranscript Unit)
   (c : AspisR1PublicPreparation.r1_wire.Challenges),
 AspisR1PublicPreparation.FinishModel.finish AspisS1ExtractedRoundChildren.children
  {IDa_Deployed.boundaries reservation with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
  call.digest call.publicValue p before c none=ok (.Ok ((S1SemanticCarrier.semanticEquiv Unit).symm sem)) := by
 obtain ⟨p,initial,after,c,_,_,_,finish⟩ :=
  NLR_SemanticFinishCaller.reached native child137 reservation i v frame domain sem returned
 have actual := NLR_FinishReservation.constructor_clause reservation
  (NLR_PrepareSemantic137.observedInput reservation i v).digest
  (NLR_PrepareSemantic137.observedInput reservation i v).publicValue p after c
  ((S1SemanticCarrier.semanticEquiv Unit).symm sem) finish
 rw [NLJ_RoundPort.rounds] at actual
 exact ⟨p,after,c,actual⟩
#print axioms source
set_option pp.proofs false
#print source
end AspisR1.NLR_PreparedSemanticClause
end
