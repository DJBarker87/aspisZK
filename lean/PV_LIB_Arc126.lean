import PV_LIB_View
import PV_LIB_Arc222
import PV_FN_THREAD_f126
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Arc126
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_THREAD_f126
abbrev Input := PV_FN_THREAD_f126_ReturnedStage.Input

def internalModel {E : Type} (x : Input E) (H : Backend E) (arc p : Address) :=
  match (PV_FN_THREAD_f222.baseReply (PV_FN_THREAD_f126_ReturnedStage.childInput x arc) H).answer with
  | .returned (.ok _) => successOut x arc p
  | _ => PV_FN_THREAD_f126_Other.after x H arc

def law {E : Type} (x : Input E) (H : Backend E) (arc p : Address)
    (out : PV_THR2_IntrinsicState.State OWNER E) : Prop := out = PV_LIB.view (internalModel x H arc p)

theorem internal_reached {E : Type} (x : Input E) (H : Backend E) (arc p : Address)
    (pre : Pre x arc p) : Reached x H arc (internalModel x H arc p) := by
  have h := (contract x H arc p pre).2
  cases ha : (PV_FN_THREAD_f222.baseReply (PV_FN_THREAD_f126_ReturnedStage.childInput x arc) H).answer with
  | pending => simpa only [ha,internalModel] using h
  | fault f => simpa only [ha,internalModel] using h
  | returned result =>
    cases result with
    | ok v =>
      have success := (show Reached x H arc (successOut x arc p) ∧ _ from
        (by simpa only [ha] using h)).1
      simpa only [internalModel,ha] using success
    | fail err => simpa only [ha,internalModel] using h
    | div => simpa only [ha,internalModel] using h

theorem realizes {E : Type} (x : Input E) (H : Backend E) (arc p : Address)
    (pre : Pre x arc p) :
    ∃ out, Reached x H arc out ∧ law x H arc p (PV_LIB.view out) :=
  ⟨internalModel x H arc p,internal_reached x H arc p pre,rfl⟩
#print axioms internal_reached
#print axioms realizes
end PV_LIB_Arc126
