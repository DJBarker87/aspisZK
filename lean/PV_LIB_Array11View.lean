import PV_LIB_Graph
import PV_FN_SLICE_f11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Array11View
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_SLICE_f11.Input
/-- Provider representations and final-store functions are used literally. -/
def internalModel {E : Type} (x : Input E) : PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.fault .abort (PV_FN_SLICE_f11.finalStore x),x.w,x.es⟩,x.stack⟩
def actual {E : Type} (x : Input E) : PV_THR2_IntrinsicState.State OWNER E :=
  PV_THR2_IntrinsicState.advance x.C x.K x.P x.H 3
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF11.program.body},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩
/-- The public abort observation has no post-state or frame fields. -/
def observe {E : Type} (q : PV_THR2_IntrinsicState.State OWNER E) :
    PV_LIB.Observation Unit (PV_THR2_IntrinsicState.State OWNER E) E :=
  match q.current.status with
  | .fault .abort _ => .abort q.current.events
  | _ => .returned () q q.current.events

def model {E : Type} (x : Input E) :
    PV_LIB.Observation Unit (PV_THR2_IntrinsicState.State OWNER E) E := .abort x.es

theorem abort_prefix {E : Type} (x : Input E) (pre : PV_FN_SLICE_f11.Pre x) :
    observe (actual x) = model x := by
  have h := (PV_FN_SLICE_f11.contract x pre).1
  change actual x = internalModel x at h
  rw [h]
  rfl
#print axioms abort_prefix
end PV_LIB_Array11View
