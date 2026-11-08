import PV_LIB_Observation
import PV_FN_THREAD_f124
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Arc124Allocated
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner R1Z.PV_FXM_ReserveWorld
open PV_FN_THREAD_f124_BoxContract PV_FN_THREAD_f124
abbrev Input := PV_FN_THREAD_f124_BoxContract.Input

def internalModel (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (sv wv : Data) :=
  let y := PV_FN_THREAD_f124_ClosedLeak.input x H resources encode shape sv wv
  let p := PV_FN_THREAD_f124_StorePost.backing x sv wv
  match (PV_FN_THREAD_f216.baseRaw y H).answer with
  | .returned (.ok _) =>
    match (PV_FN_THREAD_f216.baseForget y H).answer with
    | .returned (.ok _) =>
      match (PV_THR2_OwnUniformResourceHandler.lift H
        (.child PV_THR2_Packet124ReturnData.intoFn (x.s.nextActivation+6)
          [PV_STX2_TypedReferences.reference p .null]) y.w).answer with
      | .returned (.ok _) => successOut x H resources encode shape sv wv
      | _ => PV_FN_THREAD_f124_IntoReached.outcome x H resources encode shape sv wv
    | _ => PV_FN_THREAD_f124_LeakFailure.finish x (PV_FN_THREAD_f216.secondOut y H p)
        (PV_FN_THREAD_f216_ReturnedStage.forgetReply (PV_FN_THREAD_f216.installed y H)
          PV_THR2_Packet216Children.fn5 PV_THR2_Packet218ReturnData.allocator p)
  | _ => PV_FN_THREAD_f124_LeakFailure.finish x (PV_FN_THREAD_f216.firstOut y H)
      (PV_FN_THREAD_f216_ReturnedStage.rawReply (PV_FN_THREAD_f216.installed y H))

/-- Extract a function from the CLOSED relational case tree; no new leaf fact. -/
theorem reached (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (sv wv : Data) (heap : Nat)
    (post : Allocated x H resources encode shape sv wv heap) :
    Reached x H resources encode shape (internalModel x H resources encode shape sv wv) := by
  have h := post.2
  cases hr : (PV_FN_THREAD_f216.baseRaw (PV_FN_THREAD_f124_ClosedLeak.input x H resources encode shape sv wv) H).answer with
  | pending =>
    simpa only [internalModel,hr] using h
  | fault f =>
    simpa only [internalModel,hr] using h
  | returned result =>
    cases result with
    | fail err =>
      simpa only [internalModel,hr] using h
    | div =>
      simpa only [internalModel,hr] using h
    | ok oldRaw =>
      simp only [hr] at h
      cases hf : (PV_FN_THREAD_f216.baseForget (PV_FN_THREAD_f124_ClosedLeak.input x H resources encode shape sv wv) H).answer with
      | pending =>
        simpa only [internalModel,hr,hf] using h
      | fault f =>
        simpa only [internalModel,hr,hf] using h
      | returned result =>
        cases result with
        | fail err =>
          simpa only [internalModel,hr,hf] using h
        | div =>
          simpa only [internalModel,hr,hf] using h
        | ok oldForget =>
          simp only [hf] at h
          have j := h.2
          cases hi : (PV_THR2_OwnUniformResourceHandler.lift H
              (.child PV_THR2_Packet124ReturnData.intoFn (x.s.nextActivation+6)
                [PV_STX2_TypedReferences.reference (PV_FN_THREAD_f124_StorePost.backing x sv wv) .null]) (PV_FN_THREAD_f124_ClosedLeak.input x H resources encode shape sv wv).w).answer with
          | pending =>
            simpa only [internalModel,hr,hf,hi] using j
          | fault f =>
            simpa only [internalModel,hr,hf,hi] using j
          | returned result =>
            cases result with
            | fail err =>
              simpa only [internalModel,hr,hf,hi] using j
            | div =>
              simpa only [internalModel,hr,hf,hi] using j
            | ok oldInto =>
              simp only [hi] at j
              simpa only [internalModel,hr,hf,hi] using j.1

#print axioms reached
end PV_LIB_Arc124Allocated
