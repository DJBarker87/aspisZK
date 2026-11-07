import PV_LIB_Observation
import PV_FN_THREAD_f458Closed
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Box458
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_FN_THREAD_f458
open PV_FN_THREAD_f458Entry
abbrev Input := PV_FN_THREAD_f458.Input
def Reached {E : Type} (x : Input E) (out : PV_THR2_IntrinsicState.State OWNER E) : Prop :=
  ∃ k, PV_THR2_IntrinsicState.advance (PV_FN_THREAD_f458Entry.base x) x.K (PV_FN_THREAD_f537Run.programs x.P)
    (PV_FN_THREAD_f458Entry.handler x) k (PV_FN_THREAD_f458Entry.entry x) = out

def internalModel {E : Type} (x : Input E) :=
  match (PV_FN_THREAD_f537.reply (child x)).answer with
  | .returned (.ok unique) =>
    (⟨⟨.running ⟨{x.parent with waiting := none},x.parents,PV_FN_THREAD_f458Success.final x unique⟩,
      (PV_FN_THREAD_f537.reply (child x)).world,x.es ++ (PV_FN_THREAD_f537.reply (child x)).events⟩,x.stack⟩ : PV_THR2_IntrinsicState.State OWNER E)
  | _ => let c := child x; PV_FN_THREAD_f537Boundary.delivered (PV_FN_THREAD_f537.base c) c.s c.a (c.parent::c.parents) c.raw (PV_FN_THREAD_f537.reply c) c.es c.stack

def model {E : Type} (x : Input E) := PV_LIB.observe (internalModel x)
def law {E : Type} (x : Input E) (out : PV_LIB.MachineObservation OWNER E) : Prop := out = model x

theorem internal_reached {E : Type} (x : Input E) (pre : PV_FN_THREAD_f458.Pre x) : Reached x (internalModel x) := by
  have h := (operational_contract x pre).1.2
  cases a : (PV_FN_THREAD_f537.reply (child x)).answer with
  | pending => simpa only [Reached,internalModel,a] using h
  | fault f => simpa only [Reached,internalModel,a] using h
  | returned r =>
    cases r with
    | fail err => simpa only [Reached,internalModel,a] using h
    | div => simpa only [Reached,internalModel,a] using h
    | ok unique =>
      simpa only [Reached,internalModel,a] using h

theorem installed {E : Type} (x : Input E) (pre : PV_FN_THREAD_f458.Pre x) :
    ∃ out, Reached x out ∧ law x (PV_LIB.observe out) :=
  ⟨internalModel x,internal_reached x pre,rfl⟩
/-- Preserve the stronger CLOSED pointer theorem as the graph certificate. -/
theorem certified {E : Type} (x : Input E) (pre : PV_FN_THREAD_f458.Pre x)
    (unique612 : PV_THR2_IntrinsicSemantics_UniqueNewUnchecked612.Fact x.native) :
    (∃ out, Reached x out ∧ law x (PV_LIB.observe out)) ∧ PostWithPointer x :=
  ⟨installed x pre,contract x pre unique612⟩
#print axioms certified
#print axioms internal_reached
#print axioms installed
end PV_LIB_Box458
