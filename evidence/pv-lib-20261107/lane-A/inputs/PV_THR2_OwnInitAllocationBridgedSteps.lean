import PV_THR2_OwnInitInterpreterBridged
import PV_THR2_OwnUniformNeutral
import PV_THR2_Source361AllocationFull
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationBridgedSteps
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- Execute the actual allocation operand step with the installed allocation
handler. Failed moves retain their source frontier. No reply is fixed. -/
theorem call (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    PV_THR2_OwnInitInterpreterBridged.advance C K P resources encode H 1
      ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 129,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
    PV_THR2_IntrinsicFrameCall.after C s a parents loops
      (PV_THR2_F361.live.body.drop 130) PV_THR2_Source361AllocationFull.source.1
      PV_THR2_Source361AllocationFull.source.2.1 PV_THR2_Source361AllocationFull.source.2.2.1
      PV_THR2_Source361AllocationFull.source.2.2.2.1 PV_THR2_Source361AllocationFull.source.2.2.2.2
      w es stack := by
  let c : Config := ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 129,loops := loops},parents,s⟩
  let q : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent := ⟨⟨.running c,w,es⟩,stack⟩
  let handler := PV_THR2_OwnInitAllocationHandlerBridged.handler resources encode H
  change PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H q = _
  have interpreted : PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H q =
      PV_THR2_OwnUniformBindings.step C K P handler q := by
    have old : PV_THR2_OperatorAction.selected c = none := by
      simp [c,PV_THR2_OperatorAction.selected,
        show PV_THR2_F361.live.body.drop 129 =
          PV_THR2_F361.node162 :: PV_THR2_F361.live.body.drop 130 from rfl,
        PV_THR2_F361.node162,PV_THR2_OperatorAction.instruction]
    have action : PV_THR2_OwnInitAction.selected c = true :=
      PV_THR2_OwnInitAction.call s a parents loops
    simp only [PV_THR2_OwnInitInterpreterBridged.step,q,action,
      if_true,PV_THR2_OperatorInterpreter.step,old]
    rfl
  rw [interpreted,PV_THR2_OwnUniformNeutral.step C K P handler q (by
    intro d eq
    cases eq
    exact True.intro)]
  exact PV_THR2_IntrinsicFrameCall.run C K P handler s a parents loops
    (PV_THR2_F361.live.body.drop 130) PV_THR2_Source361AllocationFull.source.1
    PV_THR2_Source361AllocationFull.source.2.1 PV_THR2_Source361AllocationFull.source.2.2.1
    PV_THR2_Source361AllocationFull.source.2.2.2.1 PV_THR2_Source361AllocationFull.source.2.2.2.2
    w es stack (by rfl)
#print axioms call
end PV_THR2_OwnInitAllocationBridgedSteps
