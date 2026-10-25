import RowOrder_FrozenSchedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawK_ModelHead
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortFrozenOrder

theorem append_head {A : Type} (xs ys : List A) (entry : A) (h : xs.head? = some entry) :
    (xs ++ ys).head? = some entry := by
  cases xs <;> simpa using h

theorem bind_head {A B : Type} (H : Bytes → State) (p : Program Bytes State A)
    (k : A → Program Bytes State B) (entry : Bytes × State)
    (h : (eval H p).1.head? = some entry) :
    (eval H (bind p k)).1.head? = some entry := by
  rw [eval_bind]
  exact append_head _ _ _ h

theorem leaf_tag (p : Parsed) (pos : Nat) : (leaf p 0 pos).head? = some 16 := by
  simp only [leaf,ite_true,BinMerkle32Leaf.leafInput,List.head?_cons]

theorem slot_head (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144) :
    ∃ entry, (eval H (verifySlot_frozen p q 0 0)).1.head? = some entry ∧
      entry.1.head? = some 16 := by
  have len : (sortedPositions q 0 0).length = 10 := by
    simp only [sortedPositions,List.length_mergeSort,batchPositions,ite_true,List.length_range]
  cases sorted : sortedPositions q 0 0 with
  | nil => simp only [sorted,List.length_nil] at len; contradiction
  | cons pos rest =>
    refine ⟨(leaf p 0 pos,H (leaf p 0 pos)),?_,leaf_tag p pos⟩
    unfold verifySlot_frozen
    apply bind_head
    simp only [sorted,hashLeaves,eval,List.head?_cons]

theorem batch0_head (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144) :
    ∃ entry, (eval H (OraclePortFrozen2.batch p q OraclePortFrozen2.batch0)).1.head? = some entry ∧
      entry.1.head? = some 16 := by
  obtain ⟨entry,h,tag⟩ := slot_head H p q
  refine ⟨entry,?_,tag⟩
  change (eval H (bind (verifySlot_frozen p q 0 0) _)).1.head? = _
  exact bind_head H _ _ entry h

/-- No acceptance or opening premise: the first batch may reject, but its
first requested leaf is still retained. Later checkpoints and batch1 cannot
change position zero. -/
theorem decision_head (H : Bytes → State) (stored : Bytes) (tr : RawCutTranscriptRun.ErasedPrefix)
    (m : RawCutTranscriptRun.ErasedMessage) (p : Parsed) (q : Fin 22 → Fin 262144)
    (guard : OraclePortAdmission.Guard tr)
    (parsed : OraclePortStoredParserC4.parseReached stored tr = some p)
    (query : queries tr = some q) :
    ∃ entry, (eval H (OraclePortFrozen2.dV_frozen2 stored tr m)).1.head? = some entry ∧
      entry.1.head? = some 16 := by
  obtain ⟨entry,h,tag⟩ := batch0_head H p q
  refine ⟨entry,?_,tag⟩
  simp only [OraclePortFrozen2.dV_frozen2,if_pos guard,parsed,query]
  exact bind_head H _ _ entry h

#print axioms append_head
#print axioms bind_head
#print axioms leaf_tag
#print axioms slot_head
#print axioms batch0_head
#print axioms decision_head
end AspisR1.RawK_ModelHead
end
