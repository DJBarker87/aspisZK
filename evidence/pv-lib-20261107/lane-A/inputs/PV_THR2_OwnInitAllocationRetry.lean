import PV_THR2_OwnInitInterpreter
import PV_THR2_OwnUniformNeutral
import PV_THR2_IntrinsicFrameFull
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationRetry
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- Deliver the full allocation reply in the NEW interpreter at the actual
saved continuation, including every pending retry. There is no successful
reply assumption, reset, receiver or reconstructed descriptor. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (payload : Data) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (child : P PV_THR2_Source361InitChildren.fnAllocationFull = none) :
    let c := PV_THR2_IntrinsicFrameEnter.pending s a parents loops
      (PV_THR2_F361.live.body.drop 130) PV_THR2_Source361InitChildren.fnAllocationFull [payload] 45
    PV_THR2_OwnInitInterpreter.advance C K P resources encode H 1 ⟨⟨.running c,w,es⟩,stack⟩ =
      PV_THR2_IntrinsicFrameFull.received C s a parents loops
        (PV_THR2_F361.live.body.drop 130) PV_THR2_Source361InitChildren.fnAllocationFull [payload] 45
        (PV_THR2_OwnInitAllocationHandler.handler resources encode H
          (.child PV_THR2_Source361InitChildren.fnAllocationFull s.nextActivation [payload]) w) es stack := by
  intro c
  let q : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent := ⟨⟨.running c,w,es⟩,stack⟩
  let handler := PV_THR2_OwnInitAllocationHandler.handler resources encode H
  have action : PV_THR2_OwnInitAction.selected c = true :=
    PV_THR2_OwnInitAction.retry s a parents loops payload
  have old : PV_THR2_OperatorAction.selected c = none := by
    simp [c,PV_THR2_OperatorAction.selected,PV_THR2_IntrinsicFrameEnter.pending,
      PV_THR2_StaticReply.wait,
      show PV_THR2_F361.live.body.drop 130 =
        PV_THR2_F361.node163 :: PV_THR2_F361.live.body.drop 131 from rfl,
      PV_THR2_F361.node163]
  change PV_THR2_OwnInitInterpreter.step C K P resources encode H q = _
  simp only [PV_THR2_OwnInitInterpreter.step,q,action,if_true,
    PV_THR2_OperatorInterpreter.step,old]
  change PV_THR2_OwnUniformBindings.step C K P handler q = _
  rw [PV_THR2_OwnUniformNeutral.step C K P handler q (by
    intro d eq
    cases eq
    exact True.intro)]
  apply PV_THR2_IntrinsicFrameFull.run C K P handler s a parents loops
    (PV_THR2_F361.live.body.drop 130) PV_THR2_Source361InitChildren.fnAllocationFull
    [payload] 45 w es stack _ child
  apply PV_THR2_IntrinsicFrameOrdinary.run
  intro heq
  have ids := congrArg PV_THR2_OffPath.functionId heq
  cases ids
#print axioms run
end PV_THR2_OwnInitAllocationRetry
