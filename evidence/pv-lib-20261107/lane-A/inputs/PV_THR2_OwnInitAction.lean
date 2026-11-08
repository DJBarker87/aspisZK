import PV_THR2_IntrinsicFrameEnter
import PV_THR2_OperatorInterpreter
import PV_THR2_OwnInitAllocationHandler
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAction
open PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open scoped Classical
/-- The allocation call and its saved retry are the complete new action
sites at this cut. Pending allocation replies retain the same interpretation. -/
def selected (c : Config) : Bool :=
  match c.frame.completed,c.frame.waiting,c.frame.remaining with
  | none,none,.leaf (.call site fn _ _ _) :: _ =>
    decide (site.function = 361 ∧ site.statement = 14756 ∧
      fn = PV_THR2_Source361InitChildren.fnAllocationFull)
  | none,some wait,.leaf (.storage site _ _) :: _ =>
    match wait.request with
    | .child fn _ [_] => decide (site.function = 361 ∧ site.statement = 14757 ∧
        fn = PV_THR2_Source361InitChildren.fnAllocationFull)
    | _ => false
  | _,_,_ => false
/-- Syntax association at the actual allocation call; no source store read. -/
theorem call (s : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) :
    selected ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 129,loops := loops},parents,s⟩ = true := by
  simp only [selected,show PV_THR2_F361.live.body.drop 129 =
    PV_THR2_F361.node162 :: PV_THR2_F361.live.body.drop 130 from rfl,
    PV_THR2_F361.node162,PV_THR2_Source361InitChildren.fnAllocationFull,and_self,decide_true]
/-- Syntax association at the actual saved allocation retry. -/
theorem retry (s : Store Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) (payload : Data) :
    selected (PV_THR2_IntrinsicFrameEnter.pending s a parents loops
      (PV_THR2_F361.live.body.drop 130) PV_THR2_Source361InitChildren.fnAllocationFull
      [payload] 45) = true := by
  simp only [selected,PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticReply.wait,
    show PV_THR2_F361.live.body.drop 130 =
      PV_THR2_F361.node163 :: PV_THR2_F361.live.body.drop 131 from rfl,
    PV_THR2_F361.node163,and_self,decide_true]
#print axioms call
#print axioms retry
end PV_THR2_OwnInitAction
