import PV_LIB_View
import PV_FN_SLICE_f15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Array15View
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_SLICE_f15.Input
/-- Provider representations and final-store functions are used literally. -/
def internalModel {E : Type} (x : Input E) (k : PV_STX2_Syntax.Data) : PV_THR2_IntrinsicState.State OWNER E :=
  ⟨⟨.running ⟨{x.parent with waiting := none},x.parents,PV_FN_SLICE_f15.finalStore x k⟩,x.w,x.es⟩,x.stack⟩
def internalActual {E : Type} (x : Input E) : PV_THR2_IntrinsicState.State OWNER E :=
  PV_THR2_IntrinsicState.advance (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H 8
    ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF15.program.body},x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩
def model {E : Type} (x : Input E) (k : Data) := PV_LIB.view (internalModel x k)
def actual {E : Type} (x : Input E) := PV_LIB.view (internalActual x)
def law {E : Type} (x : Input E) (k : PV_STX2_Syntax.Data) (out : PV_THR2_IntrinsicState.State OWNER E) : Prop :=
  out = model x k
/-- Literal CLOSED provider instantiation; no native relation is the law. -/
theorem installed {E : Type} (x : Input E) (k : PV_STX2_Syntax.Data) (pre : PV_FN_SLICE_f15.Pre x k) :
    law x k (actual x) :=
  congrArg PV_LIB.view (PV_FN_SLICE_f15.contract x k pre).1
/-- Required-cell frame; no activation counter equality is exported. -/
theorem cells {E : Type} (x : Input E) (k : PV_STX2_Syntax.Data) (pre : PV_FN_SLICE_f15.Pre x k) :
    ∀ p : Address, p.activation ≠ x.a → p ≠ ⟨x.parent.activation,x.dest,[]⟩ → (PV_FN_SLICE_f15.finalStore x k).cells p = x.s.cells p :=
  (PV_FN_SLICE_f15.contract x k pre).2.2.1
#print axioms installed
#print axioms cells
end PV_LIB_Array15View
