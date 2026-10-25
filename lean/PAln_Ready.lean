import PAln_AlignedRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_Ready
open AspisR1.TranscriptView OraclePortStoredDecisionDraftC4
open PAln_SemanticRead

theorem of_slots (row : Nat) (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (valid : ∀ (i : Nat) (entry : LiteralTranscript.Message × LiteralTranscript.Challenge),rs[i]?=some entry → LiteralTranscript.valid (row+i) entry.1)
    (ordinary : ∀ (i : Nat) (entry : LiteralTranscript.Message × LiteralTranscript.Challenge),rs[i]?=some entry → ∃ value,entry.2.1=Value.ordinary value) :
    Ready row rs := by
  induction rs generalizing row with
  | nil => exact .nil row
  | cons entry rest ih =>
    refine .cons (by simpa using valid 0 entry rfl) (ordinary 0 entry rfl) ?_
    apply ih (row+1)
    · intro i next slot
      have h := valid (i+1) next (by simpa only [List.getElem?_cons_succ] using slot)
      simpa only [Nat.add_assoc,Nat.add_comm 1 i] using h
    · intro i next slot
      exact ordinary (i+1) next (by simpa only [List.getElem?_cons_succ] using slot)

theorem restored_valid (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (aligned : OraclePortCompactDraft.Aligned p tr)
    (row : Nat) (below : row<33) (entry : LiteralTranscript.Message × LiteralTranscript.Challenge)
    (slot : (typedRows p q tr)[row]?=some entry) : LiteralTranscript.valid row entry.1 := by
  by_cases zero : row=0
  · subst row
    obtain ⟨root,c,initial,_⟩ := aligned.2.2.2.1
    simp only [typedRows,List.getElem?_mapIdx,initial,Option.map_some,Option.some.injEq] at slot
    subst entry
    trivial
  · obtain ⟨b,c,initial,_⟩ := aligned.2.2.2.2 row (by omega) below
    simp only [typedRows,List.getElem?_mapIdx,initial,Option.map_some,Option.some.injEq] at slot
    subst entry
    exact PAln_AlignedRead.payload_valid _ row b (by omega) below

#print axioms of_slots
#print axioms restored_valid
end AspisR1.PAln_Ready
end
