import RPt_FJo_ColumnSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_BatchedWord
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
open scoped BigOperators
abbrev E := AspisWideTower.WideExact
/-- The complete 29-coordinate literal sum, on this query's decoded operands. -/
theorem value (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data E) (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (j : Fin 22) (s : Fin 4) (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2)
    (d1 : TypedRecoveredWords.decodeC1At (fun i=>packed parsed q 0 i.val) (q j)=some c1)
    (d2 : TypedRecoveredWords.decodeC2At (fun i=>packed parsed q 1 i.val) (q j)=some c2) :
    TwoFoldExtraction.batchedWord data.W data.gamma (AspisR1.childIndex (q j) s)=
      (∑ l ∈ Finset.range 26,data.gamma^l*FJl_BaseLiteral.scalar c1 s l)+
      (data.gamma^28*LiteralOpeningView.eK (c1 s).2+
        data.gamma^26*LiteralOpeningView.eK (c2 s 0)+data.gamma^27*LiteralOpeningView.eK (c2 s 1)) := by
  unfold TwoFoldExtraction.batchedWord AspisV6Width29CorrelatedAgreement.width29CurveValue
    AspisV6Width29CorrelatedAgreement.width29Batch
  apply FJo_ColumnSum.value
  · intro l
    rw [FJl_WordLane.scalar parsed q tr data read j s l c1 d1]
    simp only [FJl_BaseLiteral.scalar,Nat.mod_eq_of_lt l.isLt]
  · exact FJl_WordTails.c1 parsed q tr data read j s c1 d1
  · exact FJl_WordTails.c2first parsed q tr data read j s c2 d2
  · exact FJl_WordTails.c2second parsed q tr data read j s c2 d2
#print axioms value
end AspisR1.FJo_BatchedWord
end
