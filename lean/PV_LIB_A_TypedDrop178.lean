import PV_LIB_Observation
import PV_FN_SLICE_f7_RuntimeDrop
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_TypedDrop178
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
abbrev Input := PV_FN_SLICE_f7_RuntimeDrop.Input
/-- Exact f7 suffix from its actual typed Drop178 boundary, not all of f7. -/
def internalModel (x : Input) (capture : Data) :=
  PV_FN_SLICE_f7_AfterDrop.finish x capture
    (x.H (.drop PV_FN_SLICE_f7_AfterDrop.source.1 capture) x.w)
def model (x : Input) (capture : Data) := PV_LIB.observe (internalModel x capture)
def law (x : Input) (capture : Data) (out : PV_LIB.MachineObservation OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  out = model x capture
/-- Source projection and W5 Drop contract are supplied by the existing typed
provider. Return, fail, divergence, fault and pending are all in its run. -/
theorem installed (x : Input) (capture : Data)
    (spec : PV_FN_SLICE_RuntimeBindings.DropSemantics x.H)
    (cell : x.s.cells ⟨x.a,1,[]⟩ = some capture)
    (value : x.s.cells ⟨x.a,0,[]⟩ = some x.ptr)
    (saved : x.parent.waiting = some x.wait)
    (action : x.wait.action = .child x.a (.local x.dest))
    (pre : PV_W1_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    let r := x.H (.drop PV_FN_SLICE_f7_AfterDrop.source.1 capture) x.w
    law x capture (PV_LIB.observe (PV_THR2_IntrinsicState.advance
      (PV_FN_SLICE_ValueCarrier.carrier x.C) x.K x.P x.H
      (1+1+PV_FN_SLICE_f7_AfterDrop.steps r)
      ⟨⟨.running ⟨{activation := x.a,remaining := PV_STX2_SliceF7.program.body.drop 4},
        x.parent :: x.parents,x.s⟩,x.w,x.es⟩,x.stack⟩)) := by
  unfold law model internalModel
  dsimp only
  exact congrArg PV_LIB.observe (PV_FN_SLICE_f7_RuntimeDrop.run x capture spec cell value saved action pre)
#print axioms installed
end PV_LIB_A_TypedDrop178
