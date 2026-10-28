import PAln_RowBounds
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_Transcript
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft RawCutTranscriptRun

def message (p : Parsed) (root : State)
    (bound : ∀ row, (rowBytes p row).length≤SelectedTranscriptParams.D)
    (row : Nat) : ErasedMessage :=
  if row=0 then .initial root else .payload ⟨rowBytes p row,bound row⟩

def transcript (p : Parsed) (pub : LiteralTranscript.Public) (root : State)
    (bound : ∀ row, (rowBytes p row).length≤SelectedTranscriptParams.D)
    (challenge : Nat → LiteralTranscript.Challenge) : ErasedPrefix :=
  ⟨pub,List.ofFn (fun row : Fin 33 => (message p root bound row.val,challenge row.val))⟩

theorem rounds_length (p : Parsed) (pub : LiteralTranscript.Public) (root : State)
    (bound : ∀ row, (rowBytes p row).length≤SelectedTranscriptParams.D)
    (challenge : Nat → LiteralTranscript.Challenge) :
    (transcript p pub root bound challenge).rounds.length=33 := by
  simp only [transcript,List.length_ofFn]

theorem entry (p : Parsed) (pub : LiteralTranscript.Public) (root : State)
    (bound : ∀ row, (rowBytes p row).length≤SelectedTranscriptParams.D)
    (challenge : Nat → LiteralTranscript.Challenge) (row : Nat) (h : row<33) :
    (transcript p pub root bound challenge).rounds[row]?=
      some (message p root bound row,challenge row) := by
  simp only [transcript,List.getElem?_ofFn,h,reduceDIte]

theorem aligned (p : Parsed) (pub : LiteralTranscript.Public) (root : State)
    (bound : ∀ row, (rowBytes p row).length≤SelectedTranscriptParams.D)
    (challenge : Nat → LiteralTranscript.Challenge)
    (tag : pub.tag=p.wire[8]?.getD 0)
    (publicParsed : ∃ decoded, SemanticPublicWire.parsePublic pub.pubBytes=some decoded)
    (initial : bytes root=root0 p) : Aligned p (transcript p pub root bound challenge) := by
  refine ⟨tag,publicParsed,rounds_length _ _ _ _ _,?_,?_⟩
  · exact ⟨root,challenge 0,by simpa [message] using entry p pub root bound challenge 0 (by decide),initial⟩
  · intro row positive below
    exact ⟨⟨rowBytes p row,bound row⟩,challenge row,
      by simpa only [message,if_neg (by omega : row≠0)] using entry p pub root bound challenge row below,rfl⟩

#print axioms rounds_length
#print axioms entry
#print axioms aligned
end AspisR1.PAln_Transcript
end
