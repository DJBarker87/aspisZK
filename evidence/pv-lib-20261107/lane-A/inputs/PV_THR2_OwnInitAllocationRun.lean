import PV_THR2_OwnInitAllocationSteps
import PV_THR2_OwnInitAllocationRetry
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationRun
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- Execute allocation14756 through its arbitrary FULL resource reply in the
NEW interpreter. Uses the named operand and retry runs; does not re-prove
source allocation or any earlier trace. Every failed move/answer is retained. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (child : P PV_THR2_Source361InitChildren.fnAllocationFull = none) :
    let c : Config := ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 129,loops := loops},parents,s⟩
    PV_THR2_OwnInitInterpreter.advance C K P resources encode H
      (PV_THR2_Source361AllocationFull.cost C c w) ⟨⟨.running c,w,es⟩,stack⟩ =
      PV_THR2_Source361AllocationFull.finish C
        (PV_THR2_OwnInitAllocationHandler.handler resources encode H) c w es stack := by
  intro c
  change PV_THR2_OwnInitInterpreter.advance C K P resources encode H
    (1 + match operands C w a [.move (.local 46)] s with | none => 0 | some _ => 1)
    ⟨⟨.running c,w,es⟩,stack⟩ = _
  rw [PV_THR2_OwnInitInterpreter.advance_add,PV_THR2_OwnInitAllocationSteps.call]
  cases h : operand C s w a (.move (.local 46)) with
  | none =>
    simp only [operands,h,Bind.bind,Pure.pure,Option.bind_none,
      PV_THR2_IntrinsicFrameCall.after,PV_THR2_Source361AllocationFull.source,
      PV_THR2_F361.node162,PV_THR2_Source361AllocationFull.finish,
      PV_THR2_IntrinsicChildCall.after,c,PV_THR2_OwnInitInterpreter.advance]
  | some pair =>
    rcases pair with ⟨payload,t⟩
    simp only [operands,h,Bind.bind,Pure.pure,Option.bind_some,
      PV_THR2_IntrinsicFrameCall.after,PV_THR2_Source361AllocationFull.source,
      PV_THR2_F361.node162,PV_THR2_Source361AllocationFull.finish,
      PV_THR2_IntrinsicChildCall.after,c]
    exact PV_THR2_OwnInitAllocationRetry.run C K P resources encode H t a parents loops
      payload w es stack child
#print axioms run
end PV_THR2_OwnInitAllocationRun
