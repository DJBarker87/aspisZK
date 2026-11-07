import PV_LIB_View
import PV_FN_THREAD_f222
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Arc222
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_THREAD_f222
abbrev Input := PV_FN_THREAD_f222_ReturnedStage.Input

def internalModel {E : Type} (x : Input E) (H : Backend E) (p : Address) :=
  match (baseReply x H).answer with
  | .returned (.ok _) => successOut x p
  | _ => PV_FN_THREAD_f222_Outcomes.outcome (installed x H)

def law {E : Type} (x : Input E) (H : Backend E) (p : Address)
    (out : PV_THR2_IntrinsicState.State OWNER E) : Prop := out = PV_LIB.view (internalModel x H p)

/-- CLOSED222 supplies the actual run of this function-valued summary.
Its specialized machine is retained; original-machine transport is separate. -/
theorem internal_reached {E : Type} (x : Input E) (H : Backend E) (p : Address)
    (pre : Pre x p) : Reached x H (internalModel x H p) := by
  have h := (contract x H p pre).2
  cases ha : (baseReply x H).answer with
  | pending => simpa only [ha,internalModel] using h
  | fault f => simpa only [ha,internalModel] using h
  | returned result =>
    cases result with
    | ok v => simpa only [ha,internalModel] using h
    | fail err => simpa only [ha,internalModel] using h
    | div => simpa only [ha,internalModel] using h

theorem realizes {E : Type} (x : Input E) (H : Backend E) (p : Address)
    (pre : Pre x p) :
    ∃ out, Reached x H out ∧ law x H p (PV_LIB.view out) :=
  ⟨internalModel x H p,internal_reached x H p pre,rfl⟩
#print axioms internal_reached
#print axioms realizes
end PV_LIB_Arc222
