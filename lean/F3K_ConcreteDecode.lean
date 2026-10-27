import F3K_QueryDriverModel
import Query31ConcreteDriverTraceFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_ConcreteDecode
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge AspisV8R19.SourceDuplexStep
open Query31ExplicitScanBody
open R0C.V3

theorem accepted (blocks advances : F3K_QueryScanStep.Blocks)
    (out : Array U32 22#usize) (selected : Array U8 32#usize) (initial : State)
    (h : Query31ConcreteMaterializedSchedule.actualConcreteDecode
      Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances=ok (.Ok (out,selected))) :
    Q22.scanOut 8 Q22.q0 (blocks.val.map decodeState) (advances.val.map decodeState) initial=
      (.ok (out.val.map (fun x=>x.val)),decodeState selected) := by
  unfold Query31ConcreteMaterializedSchedule.actualConcreteDecode at h
  have source := Query31ConcreteMaterializedSchedule.adaptScanResult_success h
  have trace := AspisR1Query31Transcript.successful_driver_has_trace
    (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
    Query31ConcreteDriverTraceFacts.sourceDefaultState blocks advances out selected source
  have model := F3K_QueryDriverModel.driver blocks advances
    Query31ConcreteDriverTraceFacts.sourceDefaultState out selected initial
    Query31ConcreteDriverTraceFacts.sourceDefaultState_valid rfl trace
  rw [Query31ConcreteDriverTraceFacts.sourceDefaultState_maps_to_empty_q22] at model
  exact model

#print axioms accepted
end AspisR1.F3K_ConcreteDecode
end
