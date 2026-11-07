import PV_LIB_Observation
import PV_FN_THREAD_f443
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Box443
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_THREAD_f443 PV_FN_THREAD_f443Entry13
abbrev Input := PV_FN_THREAD_f443.Input

def internalModel {E : Type} (x : Input E) :=
  by
  classical
  exact if Returned134 x then
    if Returned344 x then
      match (q13 x).current.status with
      | .running d =>
        (⟨⟨.running ⟨{x.parent with waiting := none},x.parents,final x d⟩,
          (q13 x).current.world,(q13 x).current.events⟩,x.stack⟩ : PV_THR2_IntrinsicState.State OWNER E)
      | _ => q13 x
    else q13 x
  else q6 x

def model {E : Type} (x : Input E) := PV_LIB.observe (internalModel x)
def law {E : Type} (x : Input E) (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model x

theorem internal_reached {E : Type} (x : Input E) (pre : PV_FN_THREAD_f443.Pre x) :
    Reaches x (internalModel x) := by
  classical
  have h := (contract x pre).2.2
  by_cases a : Returned134 x
  · simp only [if_pos a] at h
    by_cases b : Returned344 x
    · simp only [if_pos b] at h
      obtain ⟨d,status,reached,frame,value⟩ := h
      simpa only [internalModel,if_pos a,if_pos b,status] using reached
    · simp only [if_neg b] at h
      simpa only [internalModel,if_pos a,if_neg b] using h.2.1
  · simp only [if_neg a] at h
    simpa only [internalModel,if_neg a] using h.2.1

theorem installed {E : Type} (x : Input E) (pre : PV_FN_THREAD_f443.Pre x) :
    ∃ out, Reaches x out ∧ law x (PV_LIB.observe out) :=
  ⟨internalModel x,internal_reached x pre,rfl⟩
#print axioms internal_reached
#print axioms installed
end PV_LIB_Box443
