import RPz7_F3J_InputRows
import Port1_StoredCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_ProofCarriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft

theorem payload_eq (p : Parsed)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D) (row : Nat) :
    Port1_StoredCarrier.payload (rowBytes p row)=⟨rowBytes p row,bound row⟩ := by
  simp only [Port1_StoredCarrier.payload,dif_pos (bound row)]

theorem erased (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (rootEq : root=fun j=>(root0 p)[j.val]?.getD 0) (row : Nat) :
    LiteralTranscript.erase (F3J_InputRows.proof p root w bound row)=
      LiteralTranscript.erase (Port1_StoredCarrier.parsedProof p row) := by
  rw [F3J_InputRows.erased]
  unfold Port1_StoredCarrier.parsedProof
  split_ifs with h0 h2 h30
  · subst row;rw [rootEq];rfl
  · rw [payload_eq];rfl
  · rw [payload_eq];rfl
  · rw [payload_eq];rfl

theorem from_parse (wire : Bytes) (p : Parsed) (parsed : parse wire=some p)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (rootEq : root=fun j=>(root0 p)[j.val]?.getD 0) (row : Nat) :
    LiteralTranscript.erase (F3J_InputRows.proof p root w bound row)=
      LiteralTranscript.erase (Port1_StoredCarrier.proof wire row) := by
  simp only [Port1_StoredCarrier.proof,parsed]
  exact erased p root w bound rootEq row

#print axioms payload_eq
#print axioms erased
#print axioms from_parse
end AspisR1.F3T_ProofCarriers
end
