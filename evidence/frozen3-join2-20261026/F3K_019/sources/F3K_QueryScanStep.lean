import F3K_QueryScanCall
import F3K_QueryIndex
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryScanStep
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SourceDuplexStep
open Query31ExplicitListLoop Query31ExplicitScanBody
open R0C.V3
abbrev Blocks := Array (Array U8 32#usize) 8#usize

theorem index_exists (a : Blocks) (i : Usize) (bound : i.val<8) :
    ∃ x,Array.index_usize a i=ok x := by
  have hi : i.val<a.val.length := by have h : a.val.length=8:=a.property;omega
  exact ⟨a.val[i.val],by simp only [Array.index_usize,Array.getElem?_Usize_eq,List.getElem?_eq_getElem hi]⟩

theorem more (blocks advances : Blocks) (i : Usize) (n : Nat)
    (s sf : Query31ModelDriverChain.QueryScan) (b x : Array U8 32#usize) (initial : State)
    (valid : validState s) (draws : (q22StateOf s).draws<64)
    (block : Array.index_usize blocks i=ok b) (advance : Array.index_usize advances i=ok x)
    (call : Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
      s b=ok (false,sf)) :
    Q22.scanOut (n+1) (q22StateOf s)
      ((blocks.val.map decodeState).drop i.val) ((advances.val.map decodeState).drop i.val) initial=
    Q22.scanOut n (q22StateOf sf)
      ((blocks.val.map decodeState).drop (i.val+1)) ((advances.val.map decodeState).drop (i.val+1)) (decodeState x) := by
  have transition := (F3K_QueryScanCall.scan s sf b false valid call).1
  rw [F3K_QueryIndex.drop_decoded blocks i b block,F3K_QueryIndex.drop_decoded advances i x advance]
  simp only [Q22.scanOut,if_pos draws,transition,Bool.false_eq_true,if_false]

theorem stop (blocks advances : Blocks) (i : Usize) (n : Nat)
    (s sf : Query31ModelDriverChain.QueryScan) (b x : Array U8 32#usize) (initial : State)
    (valid : validState s) (draws : (q22StateOf s).draws<64)
    (block : Array.index_usize blocks i=ok b) (advance : Array.index_usize advances i=ok x)
    (call : Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
      s b=ok (true,sf)) :
    Q22.scanOut (n+1) (q22StateOf s)
      ((blocks.val.map decodeState).drop i.val) ((advances.val.map decodeState).drop i.val) initial=
    (AspisV8R19.Q22WordScan.finish (q22StateOf sf),decodeState x) := by
  have transition := (F3K_QueryScanCall.scan s sf b true valid call).1
  rw [F3K_QueryIndex.drop_decoded blocks i b block,F3K_QueryIndex.drop_decoded advances i x advance]
  simp only [Q22.scanOut,if_pos draws,transition,if_true]

theorem progress (s sf : Query31ModelDriverChain.QueryScan) (b : Array U8 32#usize)
    (valid : validState s)
    (call : Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
      s b=ok (false,sf)) : (q22StateOf sf).draws=(q22StateOf s).draws+8 := by
  have transition := (F3K_QueryScanCall.scan s sf b false valid call).1
  have progress := AspisV8R19.Q22WordScan.scan_progress (q22StateOf s)
    (AspisV8R19.SamplerWords.words 18 (decodeState b))
    (by rw [transition])
  rw [transition,AspisV8R19.SamplerWords.words_length] at progress
  exact progress

#print axioms index_exists
#print axioms more
#print axioms stop
#print axioms progress
end AspisR1.F3K_QueryScanStep
end
