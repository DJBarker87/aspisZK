import PV_LIB_View
import PV_FN_THREAD_f315
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Thread315
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_THREAD_f315.Input
/-- SAME provider final Store; counter is not an interface equality. -/
def internalModel {E : Type} (x : Input E) : PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.running ⟨{x.parent with waiting := none},x.parents,PV_FN_THREAD_f315.finalStore x⟩,x.w,x.es⟩,x.stack⟩
def internalActual {E : Type} (x : Input E) : PV_THR2_IntrinsicState.State OWNER E :=
  PV_THR2_IntrinsicState.advance (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
    x.K x.P x.H 15
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_THR2_F315.live.body},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩
def model {E : Type} (x : Input E) := PV_LIB.view (internalModel x)
def actual {E : Type} (x : Input E) := PV_LIB.view (internalActual x)
def law {E : Type} (x : Input E) (out : PV_THR2_IntrinsicState.State OWNER E) : Prop := out = model x
theorem installed {E : Type} (x : Input E) (pre : PV_FN_THREAD_f315.Pre x) : law x (actual x) :=
  congrArg PV_LIB.view (PV_FN_THREAD_f315.contract x pre).1
#print axioms installed
end PV_LIB_Thread315
