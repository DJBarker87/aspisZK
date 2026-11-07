import PV_LIB_Observation
import PV_FN_THREAD_f537Contract
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Box537
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_THREAD_f537
abbrev Input := PV_FN_THREAD_f537.Input

def internalModel {E : Type} (x : Input E) :=
  match (reply x).answer with
  | .returned (.ok unique) =>
    (⟨⟨.running ⟨{x.parent with waiting := none},x.parents,PV_FN_THREAD_f537Frame.final x.s x.a x.parent.activation 0 x.raw unique x.allocator⟩,
      (reply x).world,x.es ++ (reply x).events⟩,x.stack⟩ : PV_THR2_IntrinsicState.State OWNER E)
  | _ => PV_FN_THREAD_f537Boundary.delivered (base x) x.s x.a (x.parent::x.parents) x.raw (reply x) x.es x.stack

def model {E : Type} (x : Input E) := PV_LIB.observe (internalModel x)
def law {E : Type} (x : Input E) (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model x

theorem internal_reached {E : Type} (x : Input E) (pre : Pre x) : Reaches x (internalModel x) := by
  have h := (contract x pre).1.2
  cases a : (reply x).answer with
  | pending => simpa only [internalModel,a] using h
  | fault f => simpa only [internalModel,a] using h
  | returned r =>
    cases r with
    | fail err => simpa only [internalModel,a] using h
    | div => simpa only [internalModel,a] using h
    | ok unique =>
      simp only [a] at h
      simpa only [internalModel,a] using h.1

theorem installed {E : Type} (x : Input E) (pre : Pre x) :
    ∃ out, Reaches x out ∧ law x (PV_LIB.observe out) :=
  ⟨internalModel x,internal_reached x pre,rfl⟩
#print axioms internal_reached
#print axioms installed
end PV_LIB_Box537
