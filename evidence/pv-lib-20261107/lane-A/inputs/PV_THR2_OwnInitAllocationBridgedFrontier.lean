import PV_THR2_OwnInitAllocationBridgedRun
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationBridgedFrontier
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- Install allocation interpretation at the supplied ACTUAL state. The
retained source frontier selector keeps every unrelated or failed frontier;
there is no registration or world reconstruction at this boundary. -/
def after (C : Carrier OWNER Data) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (q : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent) :=
  PV_THR2_Source361AllocationFull.after C
    (PV_THR2_OwnInitAllocationHandlerBridged.handler resources encode H) q
/-- Apply the already proved full allocation run at whichever actual state
the joined trace supplies, with source running/ready cases eliminated inside
this theorem. All zero-fuel, operand-failure and FULL reply cases remain. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (q : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
    (child : P PV_THR2_Source361InitChildren.fnAllocationFull = none) :
    PV_THR2_OwnInitInterpreterBridged.advance C K P resources encode H
      (PV_THR2_Source361AllocationFull.steps C q) q = after C resources encode H q := by
  classical
  rcases q with ⟨⟨status,w,es⟩,stack⟩
  cases status with
  | running c =>
    by_cases ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 129) c
    · rw [PV_THR2_IntrinsicAtContinuation.frame c ready]
      have fresh : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 129)
          ⟨{activation := c.frame.activation,remaining := PV_THR2_F361.live.body.drop 129,loops := c.frame.loops},c.callers,c.store⟩ :=
        ⟨rfl,rfl,rfl,rfl⟩
      simp only [PV_THR2_Source361AllocationFull.steps,after,PV_THR2_Source361AllocationFull.after,
        PV_THR2_IntrinsicAtContinuation.steps,PV_THR2_IntrinsicAtContinuation.after,if_pos fresh]
      exact PV_THR2_OwnInitAllocationBridgedRun.run C K P resources encode H c.store c.frame.activation
        c.callers c.frame.loops w es stack child
    · simp only [PV_THR2_Source361AllocationFull.steps,after,PV_THR2_Source361AllocationFull.after,
        PV_THR2_IntrinsicAtContinuation.steps,PV_THR2_IntrinsicAtContinuation.after,if_neg ready,
        PV_THR2_OwnInitInterpreterBridged.advance]
  | returned r s => rfl
  | fault f s => rfl
  | undefined site s => rfl
#print axioms run
end PV_THR2_OwnInitAllocationBridgedFrontier
