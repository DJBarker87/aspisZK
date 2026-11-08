import PV_LIB_Arc124Allocated
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Arc124
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner R1Z.PV_FXM_ReserveWorld
open PV_FN_THREAD_f124_BoxContract PV_FN_THREAD_f124
abbrev Input := PV_FN_THREAD_f124_BoxContract.Input

def internalModel (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape) :=
  match (strong x H).answer with
  | .returned (.ok sv) =>
    match (weak x H).answer with
    | .returned (.ok wv) =>
      match (resources (.malloc shape.layout.width) (world (weak x H).world)).answer with
      | .returned (.ok heap) => if heap = 0 then
          PV_FN_THREAD_f124_Interface.allocationOut x H resources encode shape sv wv
        else PV_LIB_Arc124Allocated.internalModel x H resources encode shape sv wv
      | _ => PV_FN_THREAD_f124_Interface.allocationOut x H resources encode shape sv wv
    | _ => PV_FN_THREAD_f124_Interface.secondOut x H sv
  | _ => PV_FN_THREAD_f124_Interface.firstOut x H

def model (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape) :=
  PV_LIB.observe (internalModel x H resources encode shape)
def law (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model x H resources encode shape

theorem internal_reached (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (pre : Pre x) : Reached x H resources encode shape (internalModel x H resources encode shape) := by
  have h := (contract x H resources encode shape pre).2
  cases hs : (strong x H).answer with
  | pending =>
    simpa only [internalModel,hs] using h
  | fault f =>
    simpa only [internalModel,hs] using h
  | returned result =>
    cases result with
    | fail err =>
      simpa only [internalModel,hs] using h
    | div =>
      simpa only [internalModel,hs] using h
    | ok sv =>
      simp only [hs] at h
      have j := h.2
      cases hw : (weak x H).answer with
      | pending =>
        simpa only [internalModel,hs,hw] using j
      | fault f =>
        simpa only [internalModel,hs,hw] using j
      | returned result =>
        cases result with
        | fail err =>
          simpa only [internalModel,hs,hw] using j
        | div =>
          simpa only [internalModel,hs,hw] using j
        | ok wv =>
          simp only [hw] at j
          have k := j.2
          cases ha : (resources (.malloc shape.layout.width) (world (weak x H).world)).answer with
          | pending =>
            simpa only [internalModel,hs,hw,ha] using k
          | fault f =>
            simpa only [internalModel,hs,hw,ha] using k
          | returned result =>
            cases result with
            | fail err =>
              simpa only [internalModel,hs,hw,ha] using k
            | div =>
              simpa only [internalModel,hs,hw,ha] using k
            | ok heap =>
              simp only [ha] at k
              by_cases zero : heap = 0
              · simpa only [internalModel,hs,hw,ha,if_pos zero] using k
              · have allocated : Allocated x H resources encode shape sv wv heap := by
                  simpa only [if_neg zero] using k
                simpa only [internalModel,hs,hw,ha,if_neg zero] using
                  PV_LIB_Arc124Allocated.reached x H resources encode shape sv wv heap allocated

theorem installed (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (pre : Pre x) : ∃ out, Reached x H resources encode shape out ∧
      law x H resources encode shape (PV_LIB.observe out) :=
  ⟨internalModel x H resources encode shape,internal_reached x H resources encode shape pre,rfl⟩
#print axioms internal_reached
#print axioms installed
end PV_LIB_Arc124
