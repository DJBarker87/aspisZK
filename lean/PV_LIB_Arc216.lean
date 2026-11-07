import PV_LIB_Observation
import PV_LIB_PureLeaves
import PV_FN_THREAD_f216
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Arc216
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_THREAD_f216
abbrev Input := PV_FN_THREAD_f216_ReturnedStage.Input

def internalModel {E : Type} (x : Input E) (H : Backend E) (p : Address) :=
  match (baseRaw x H).answer with
  | .returned (.ok _) =>
    match (baseForget x H).answer with
    | .returned (.ok _) => successOut x p
    | _ => secondOut x H p
  | _ => firstOut x H

def model {E : Type} (x : Input E) (H : Backend E) (p : Address) :=
  PV_LIB.observe (internalModel x H p)
def law {E : Type} (x : Input E) (H : Backend E) (p : Address)
    (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model x H p

theorem internal_reached {E : Type} (x : Input E) (H : Backend E) (p : Address)
    (pre : Pre x p) : Reached x H (internalModel x H p) := by
  have h := (contract x H p pre).2.2
  cases ha : (baseRaw x H).answer with
  | pending => simpa only [internalModel,ha] using h
  | fault f => simpa only [internalModel,ha] using h
  | returned result =>
    cases result with
    | fail err => simpa only [internalModel,ha] using h
    | div => simpa only [internalModel,ha] using h
    | ok v =>
      cases hb : (baseForget x H).answer with
      | pending => simpa only [internalModel,ha,hb] using h
      | fault f => simpa only [internalModel,ha,hb] using h
      | returned second =>
        cases second with
        | ok value => simpa only [internalModel,ha,hb] using h
        | fail err => simpa only [internalModel,ha,hb] using h
        | div => simpa only [internalModel,ha,hb] using h

theorem installed {E : Type} (x : Input E) (H : Backend E) (p : Address)
    (pre : Pre x p) :
    ∃ out, Reached x H out ∧ law x H p (PV_LIB.observe out) :=
  ⟨internalModel x H p,internal_reached x H p pre,rfl⟩

#print axioms internal_reached
#print axioms installed
end PV_LIB_Arc216
