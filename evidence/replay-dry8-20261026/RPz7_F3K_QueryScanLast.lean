import RPz7_F3K_QueryScanStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryScanLast
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SourceDuplexStep
open Query31ExplicitListLoop Query31ExplicitScanBody
open R0C.V3

theorem last (blocks advances : F3K_QueryScanStep.Blocks) (i : Usize)
    (s sf : Query31ModelDriverChain.QueryScan) (b x : Array U8 32#usize) (initial : State)
    (valid : validState s) (draws : (q22StateOf s).draws<64)
    (block : Array.index_usize blocks i=ok b) (advance : Array.index_usize advances i=ok x)
    (stop : Bool)
    (call : Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
      s b=ok (stop,sf)) :
    Q22.scanOut 1 (q22StateOf s)
      ((blocks.val.map decodeState).drop i.val) ((advances.val.map decodeState).drop i.val) initial=
    (AspisV8R19.Q22WordScan.finish (q22StateOf sf),decodeState x) := by
  have transition := (F3K_QueryScanCall.scan s sf b stop valid call).1
  rw [F3K_QueryIndex.drop_decoded blocks i b block,F3K_QueryIndex.drop_decoded advances i x advance]
  cases stop <;> simp only [Q22.scanOut,if_pos draws,transition,Bool.false_eq_true,if_false,if_true]

#print axioms last
end AspisR1.F3K_QueryScanLast
end
