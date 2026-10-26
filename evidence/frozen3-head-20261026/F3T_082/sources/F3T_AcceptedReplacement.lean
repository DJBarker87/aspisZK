import F3T_AcceptedParser
import F3T_PrefixCongr
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_AcceptedReplacement
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft

def replace (i : F3_Model.Input) : F3_Model.Input :=
  {i with proof:=Port1_StoredCarrier.proof i.stored}

theorem program (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input)
    (accepted : (eval H (F3_Model.verifier D i)).2=true) :
    F3_Model.verifier D i=F3_Model.verifier D (replace i) := by
  obtain ⟨p,parsed,wire,aligned⟩ := F3T_AcceptedParser.parsed D H i accepted
  apply F3T_PrefixCongr.verifier_congr D i (replace i) rfl rfl rfl
  intro row below
  change LiteralTranscript.erase (i.proof row)=LiteralTranscript.erase (Port1_StoredCarrier.proof i.stored row)
  simp only [Port1_StoredCarrier.proof,parsed]
  exact F3T_AlignedRows.canonical_rows D H i.semantic.value i.proof p aligned
    (F3T_ParsedRows.bounds i.stored p parsed) row below

#print axioms program
end AspisR1.F3T_AcceptedReplacement
end
