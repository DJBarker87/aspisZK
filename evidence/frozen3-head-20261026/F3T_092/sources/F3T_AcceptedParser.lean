import F3T_ParsedRows
import F3T_Decision
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_AcceptedParser
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft

theorem parsed (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input)
    (accepted : (eval H (F3_Model.verifier D i)).2=true) :
    ∃ p,parse i.stored=some p ∧ p.wire=i.stored ∧ Aligned p
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H i.semantic.value i.proof 33)) := by
  change (eval H (OracleDecisionFeasibilityCore.verifier D
    (F3_Model.decision i.physical i.stored) i.semantic.value i.proof)).2=true at accepted
  rw [OracleDecisionFeasibilityBudget.verifier_eval] at accepted
  have terminal : (eval H (F3_Model.decision i.physical i.stored
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H i.semantic.value i.proof 33))
      (LiteralTranscript.erase (i.proof 33)))).2=true := accepted
  obtain ⟨guard,p,q,input,parser,rest⟩ := F3T_Decision.accepted_details i.physical i.stored _ _ H terminal
  exact ⟨p,OraclePortStoredParserC4.parsed _ _ _ parser⟩

theorem tag (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input)
    (accepted : (eval H (F3_Model.verifier D i)).2=true) : i.semantic.value.tag=2 := by
  change (eval H (OracleDecisionFeasibilityCore.verifier D
    (F3_Model.decision i.physical i.stored) i.semantic.value i.proof)).2=true at accepted
  rw [OracleDecisionFeasibilityBudget.verifier_eval] at accepted
  have terminal : (eval H (F3_Model.decision i.physical i.stored
      (LiteralTranscript.erasePrefix ((LiteralByteProtocol.protocol D).transcript H i.semantic.value i.proof 33))
      (LiteralTranscript.erase (i.proof 33)))).2=true := accepted
  have guard := (F3T_Decision.accepted_details i.physical i.stored _ _ H terminal).1
  rw [InitialTagDecision.erased_transcript_tag] at guard
  exact guard.1

#print axioms tag
#print axioms parsed
end AspisR1.F3T_AcceptedParser
end
