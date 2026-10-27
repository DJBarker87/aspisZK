import FJo_BatchedWord
import FJo_FourLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_BatchedFormula
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
open scoped BigOperators
abbrev E := AspisWideTower.WideExact
attribute [local irreducible] TwoFoldExtraction.batchedWord FJo_FourLiteral.formula
/-- The complete 29-coordinate literal sum, on this query's decoded operands. -/
theorem value (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data E) (read : LiteralMatchingData.read (typedRows parsed q tr)=some data)
    (j : Fin 22) (s : Fin 4) (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2)
    (d1 : TypedRecoveredWords.decodeC1At (fun i=>packed parsed q 0 i.val) (q j)=some c1)
    (d2 : TypedRecoveredWords.decodeC2At (fun i=>packed parsed q 1 i.val) (q j)=some c2) :
    TwoFoldExtraction.batchedWord data.W data.gamma (AspisR1.childIndex (q j) s)=
      FJo_FourLiteral.formula data.gamma c1 c2 s := by
  unfold FJo_FourLiteral.formula
  with_reducible exact FJo_BatchedWord.value parsed q tr data read j s c1 c2 d1 d2
#print axioms value
end AspisR1.FJo_BatchedFormula
end
