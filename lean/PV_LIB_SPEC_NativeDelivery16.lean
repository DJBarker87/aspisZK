import PV_LIB_SPEC_Tls64Data16
import PV_THR2_ExecutionBoundary
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_NativeDelivery16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen

/-- Contract-first full native delivery on v2. All statuses, worlds and events
are retained by the named existing full_reply theorem. No callee is unfolded. -/
theorem full (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (c : Config) (w : OWNER) (events : List Event) (suspended : List Config)
    (wait : PV_STX2_Native.Waiting Data) (fn : Data) (a dest : Nat) (args : List Data)
    (quiet : PV_LIB_SPEC_SourceTransport15.Quiet ⟨⟨.running c,w,events⟩,suspended⟩)
    (intrinsic : PV_THR2_Catch316Segment.select c = none)
    (action : wait.action = .child a (.local dest))
    (done : c.frame.completed = none) (saved : c.frame.waiting = some wait)
    (request : wait.request = .child fn a args)
    (child : PV_LIB_SPEC_Full.programs fn = none) :
    let q := PV_THR2_ChildBoundary.delivered (runtime p).carrier c wait
      (PV_LIB_SPEC_ReachedNative14.handler cut p c wait.request w)
    PV_LIB_SPEC_ReachedNative14.transition cut p c ⟨⟨.running c,w,events⟩,suspended⟩ =
      ⟨⟨q.status,q.world,events ++ q.events⟩,suspended⟩ := by
  rw [PV_LIB_SPEC_SourceTransport15.transition cut p c _
    (PV_LIB_SPEC_ReachedNative14.handler cut p c) quiet]
  · simp only [PV_THR2_IntrinsicState.step,intrinsic]
    rw [PV_THR2_ExecutionBoundary.full_reply _ _ _ _ c wait fn a dest args w
      action done saved request child]
  · intro frame hf r hr
    rfl

#print axioms full
end PV_LIB_SPEC_NativeDelivery16
