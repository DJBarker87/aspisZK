import F3_Model
import RPz7_PAln_RowBounds
import RPz7_PAln_Physical
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_InputRows
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft

def proof (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row, (rowBytes p row).length ≤ SelectedTranscriptParams.D) :
    RawCutProverCompiler.Proof := fun row =>
  let b : LiteralTranscript.BytesMessage := ⟨rowBytes p row,bound row⟩
  if row = 0 then .initial root w.c1
  else if row = 2 then .c2 b w.c2
  else if row = 30 then .second b w.final
  else .payload b

theorem erased (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row, (rowBytes p row).length ≤ SelectedTranscriptParams.D) (row : Nat) :
    LiteralTranscript.erase (proof p root w bound row) =
      if row=0 then .initial root else .payload ⟨rowBytes p row,bound row⟩ := by
  unfold proof
  split_ifs <;> rfl

theorem valid (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row, (rowBytes p row).length ≤ SelectedTranscriptParams.D)
    (row : Nat) (below : row < 33) : LiteralTranscript.valid row (proof p root w bound row) := by
  unfold proof
  split_ifs with h0 h2 h30
  · subst row; trivial
  · subst row; trivial
  · subst row; trivial
  · cases row with
    | zero => contradiction
    | succ row =>
      cases row with
      | zero => exact ⟨by decide,by decide,by decide,below⟩
      | succ row =>
        cases row with
        | zero => contradiction
        | succ row =>
          simp only [LiteralTranscript.valid]
          exact ⟨by omega,by omega,by omega,below⟩

def input (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row, (rowBytes p row).length ≤ SelectedTranscriptParams.D)
    (semantic : LiteralTranscript.Public) (physical : Bytes) : F3_Model.Input :=
  ⟨⟨semantic⟩,⟨physical⟩,proof p root w bound,p.wire⟩

#print axioms erased
#print axioms valid
end AspisR1.F3J_InputRows
end
