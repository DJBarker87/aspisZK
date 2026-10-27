import RPz8_F3T_AcceptedReplacement
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_AcceptedRows
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem stored (D : LiteralByteProtocol.Decoder) (H : Bytes → State) (i : F3_Model.Input)
    (accepted : (eval H (F3_Model.verifier D i)).2 = true) :
    ∀ row, row < 33 → LiteralTranscript.erase (i.proof row) =
      LiteralTranscript.erase (Port1_StoredCarrier.proof i.stored row) := by
  obtain ⟨p,parsed,wire,aligned⟩ := F3T_AcceptedParser.parsed D H i accepted
  intro row below
  simp only [Port1_StoredCarrier.proof,parsed]
  exact F3T_AlignedRows.canonical_rows D H i.semantic.value i.proof p aligned
    (F3T_ParsedRows.bounds i.stored p parsed) row below

#print axioms stored
end AspisR1.ARQ_AcceptedRows
end
