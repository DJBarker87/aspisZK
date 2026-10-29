import PV_B3P_UsizeLoop9227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_Binding9227 Result ControlFlow
set_option autoImplicit false
/-- Range<usize>::spec_next, for the TrustedStep specialization. The pure
unchecked increment's precondition is established by range_increment_safe13. -/
def range_next13 (start finish : Usize) : Result (Option Usize × Usize) :=
  if start < finish then .ok (some start,Usize.wrapping_add start 1#usize)
  else .ok (none,start)

theorem range_increment_safe13 (start finish : Usize) (h : start < finish) :
    start.val+1 < UScalar.size .Usize := by
  have hf : finish.val < UScalar.size .Usize := by simpa only [UScalar.size] using finish.hBounds
  have hs : start.val < finish.val := by scalar_tac
  omega

/-- Range<usize> has only two usize fields and no custom destructor. This is
its structural cleanup model, not a claim about an arbitrary Drop type. -/
def range_drop13 {α : Type} (_start _finish : Usize) (state : α) : Result α := .ok state

def range_body13 {α : Type} (step : α → Usize → Result α) (finish : Usize)
    (state : α × Usize) : Result (ControlFlow (α × Usize) α) := do
  let (item,next) ← range_next13 state.2 finish
  match item with
  | none =>
    let state1 ← range_drop13 next finish state.1
    .ok (.done state1)
  | some index =>
    let state1 ← step state.1 index
    .ok (.cont (state1,next))

theorem range_body_binding13 {α : Type} (step : α → Usize → Result α)
    (finish : Usize) (state : α × Usize) :
    range_body13 step finish state = usize_body step finish state := by
  unfold range_body13 range_next13 usize_body
  split <;> simp only [bind_tc_ok,range_drop13,lift]

def range_loop13 {α : Type} (step : α → Usize → Result α) (start finish : Usize) (state : α) : Result α :=
  loop (range_body13 step finish) (state,start)

theorem range_loop_binding13 {α : Type} (step : α → Usize → Result α)
    (start finish : Usize) (state : α) :
    range_loop13 step start finish state = loop (usize_body step finish) (state,start) := by
  unfold range_loop13
  have bodies : range_body13 step finish = usize_body step finish := funext (range_body_binding13 step finish)
  exact congrArg (fun body => loop body (state,start)) bodies

theorem range_plan13 {α : Type} (step : α → Usize → Result α)
    (start finish : Usize) (n : Nat) (state : α) (h : start.val+n=finish.val) :
    range_loop13 step start finish state = usize_plan step n start state :=
  Eq.trans (range_loop_binding13 step start finish state) (usize_loop_plan step finish start n state h)

theorem range_drop_binding13 {α : Type} (start finish : Usize) (state : α) :
    range_drop13 start finish state = .ok state := rfl

#print axioms range_increment_safe13
#print axioms range_body_binding13
#print axioms range_loop_binding13
#print axioms range_plan13
#print axioms range_drop_binding13
end PV_B3P_Binding13227
