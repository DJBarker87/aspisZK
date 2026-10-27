import FJo_AdaptedDots
import FJo_BatchedFormula
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_DotsBatched
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
attribute [local irreducible] TwoFoldExtraction.batchedWord FJo_FourLiteral.formula
/-- Backend values equal the complete literal batched word on the SAME bytes. -/
theorem value (opening : Slice U8) (g : Array FIp_DotsAdapter.E 29#usize)
    (out : Array FIp_DotsAdapter.E 4#usize)
    (parsed : Parsed) (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (data : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data) (j : Fin 22)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g))
    (powers : ∀ l : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) l.val=data.gamma^l.val)
    (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2)
    (d1 : MixedLeafDecoder.decodeC1 ((bytesOf opening.val).take 480)=some c1)
    (d2 : MixedLeafDecoder.decodeC2 (((bytesOf opening.val).drop 480).take 128)=some c2)
    (p1 : TypedRecoveredWords.decodeC1At (fun i=>packed parsed q 0 i.val) (q j)=some c1)
    (p2 : TypedRecoveredWords.decodeC2At (fun i=>packed parsed q 1 i.val) (q j)=some c2)
    (run : FIp_DotsAdapter.dots opening g=ok out) :
    Port5Q1_OpeningValues.values out=FirstFold.fibre (TwoFoldExtraction.batchedWord data.W data.gamma) (q j) := by
  funext s
  unfold FirstFold.fibre
  have native := FJo_AdaptedDots.value opening g out data.gamma hg powers c1 c2 d1 d2 run s
  have literal := FJo_BatchedFormula.value parsed q tr data read j s c1 c2 p1 p2
  with_reducible exact native.trans literal.symm
#print axioms value
end AspisR1.FJo_DotsBatched
end
