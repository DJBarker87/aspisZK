import RawK_ModelHead
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_ModelAll
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Total first-position classification, including admission/parser/sampler
exits and both rejecting Merkle prefixes. No model acceptance premise. -/
theorem first (H : Bytes → State) (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix)
    (m : RawCutTranscriptRun.ErasedMessage) :
    (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).1.head? = none ∨
    ∃ entry, (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).1.head? = some entry ∧
      entry.1.head? = some 16 := by
  by_cases guard : OraclePortAdmission.Guard tr
  · cases parsed : OraclePortStoredParserC4.parseReached stored tr with
    | none => left; simp only [OraclePortFrozen2.dV_frozen2,if_pos guard,parsed,eval,List.head?_nil]
    | some p =>
      cases query : OraclePortSelectedDraft.queries tr with
      | none => left; simp only [OraclePortFrozen2.dV_frozen2,if_pos guard,parsed,query,eval,List.head?_nil]
      | some q => exact Or.inr (RawK_ModelHead.decision_head H stored tr m p q guard parsed query)
  · left; simp only [OraclePortFrozen2.dV_frozen2,if_neg guard,eval,List.head?_nil]

theorem different (H : Bytes → State) (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix)
    (m : RawCutTranscriptRun.ErasedMessage) (entry : Bytes × State)
    (tag : entry.1.head? = some 85) :
    (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).1.head? ≠ some entry := by
  intro same
  rcases first H stored tr m with empty | ⟨model,h,modelTag⟩
  · rw [empty] at same; cases same
  · have eq : model = entry := Option.some.inj (h.symm.trans same)
    subst model
    have impossible : (some (16 : Fin 256)) = some 85 := modelTag.symm.trans tag
    have bad : (16 : Fin 256) = 85 := Option.some.inj impossible
    exact (by decide : (16 : Fin 256) ≠ 85) bad

#print axioms first
#print axioms different
end AspisR1.RawK_ModelAll
end
