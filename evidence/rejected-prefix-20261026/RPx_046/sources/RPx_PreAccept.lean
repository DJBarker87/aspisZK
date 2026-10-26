import RPx_Schedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_PreAccept
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open RawCutTranscriptRun

theorem guard_reject (H : Bytes → State) (physical : F3_Model.PhysicalPublic) (stored : Bytes)
    (tr : ErasedPrefix) (m : ErasedMessage) (guard : ¬OraclePortAdmission.Guard tr) :
    eval H (F3_Model.decision physical stored tr m)=([],false) := by
  simp only [F3_Model.decision,if_neg guard,eval]

theorem parse_reject (H : Bytes → State) (physical : F3_Model.PhysicalPublic) (stored : Bytes)
    (tr : ErasedPrefix) (m : ErasedMessage) (guard : OraclePortAdmission.Guard tr)
    (parsed : OraclePortStoredParserC4.parseReached stored tr=none) :
    eval H (F3_Model.decision physical stored tr m)=([],false) := by
  simp only [F3_Model.decision,if_pos guard,parsed,eval]

/-- A pre-decision rejection does not erase the complete sampler prefix. -/
theorem complete (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input) :
    eval H (F3_Model.verifier D i) =
      let tr := (LiteralByteProtocol.protocol D).transcript H i.semantic.value i.proof 33
      let terminal := eval H (OracleDecisionFeasibilityCore.onBytes
        (F3_Model.decision i.physical i.stored) tr (i.proof 33))
      ((((List.range 33).map fun j => (eval H
        ((LiteralByteProtocol.protocol D).chain H i.semantic.value i.proof j).toProgram).1).flatten
        ++ terminal.1),terminal.2) := F3_Model.complete_schedule D H i

#print axioms guard_reject
#print axioms parse_reject
#print axioms complete
end AspisR1.RPx_PreAccept
end
