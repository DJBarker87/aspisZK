import PV_B3P_ClosureLinks14227
namespace PV_B3Q_Range
open Aeneas Aeneas.Std PV_B3P_Groups14227 PV_B3P_Binding13227
set_option autoImplicit false
structure State where
 start : Usize
 finish : Usize
structure Reverse where
 iter : State
/-- TrustedStep<usize> RangeIteratorImpl::spec_next: save start before updating it. -/
def source_next (range : State) : Result (Option Usize × State) :=
 if range.start < range.finish then
   let old := range.start
   let advanced := Usize.wrapping_add old 1#usize
   .ok (some old,{start := advanced,finish := range.finish})
 else .ok (none,range)
def model_next (range : State) : Result (Option Usize × State) := do
 let (item,advanced) ← range_next13 range.start range.finish
 .ok (item,{start := advanced,finish := range.finish})
theorem next_binding (range : State) : source_next range = model_next range := by
 cases range
 unfold source_next model_next range_next13
 split <;> rfl
/-- Reverse iteration stores the decremented END, so mixed front/back iteration
cannot repeat the consumed end slot. -/
def source_back (range : State) : Result (Option Usize × State) :=
 if range.start < range.finish then
   let previous := Usize.wrapping_sub range.finish 1#usize
   .ok (some previous,{start := range.start,finish := previous})
 else .ok (none,range)
def model_back (range : State) : Result (Option Usize × State) :=
 if range.start < range.finish then
   .ok (some (Usize.wrapping_sub range.finish 1#usize),
     {start := range.start,finish := Usize.wrapping_sub range.finish 1#usize})
 else .ok (none,range)
theorem back_binding (range : State) : source_back range = model_back range := rfl

def source_rev (reverse : Reverse) : Result (Option Usize × Reverse) := do
 let (item,advanced) ← source_back reverse.iter
 .ok (item,{iter := advanced})
def model_rev (reverse : Reverse) : Result (Option Usize × Reverse) := do
 let (item,advanced) ← model_back reverse.iter
 .ok (item,{iter := advanced})
theorem rev_binding (reverse : Reverse) : source_rev reverse = model_rev reverse := by
 unfold source_rev model_rev
 rw [back_binding]

theorem forward_precondition (range : State) (active : range.start < range.finish) :
    range.start.val+1 < UScalar.size .Usize :=
 range_increment_safe13 range.start range.finish active
theorem backward_precondition (range : State) (active : range.start < range.finish) :
    1 ≤ range.finish.val := by scalar_tac
theorem backward_value (range : State) (active : range.start < range.finish) :
    (Usize.wrapping_sub range.finish 1#usize).val = range.finish.val-1 :=
 PV_B3P_Offset226V3.sub_value range.finish 1#usize (by
   change 1 ≤ range.finish.val
   exact backward_precondition range active)

inductive Body where | next | back | rev | into_iter | reverse_new | drop
def Signature : Body → Type
 | .next | .back => State → Result (Option Usize × State)
 | .rev => Reverse → Result (Option Usize × Reverse)
 | .into_iter => State → Result State
 | .reverse_new => State → Result Reverse
 | .drop => State → Result Unit
def source : (body : Body) → Signature body
 | .next => source_next
 | .back => source_back
 | .rev => source_rev
 | .into_iter => fun range => .ok range
 | .reverse_new => fun range => .ok ⟨range⟩
 | .drop => fun _ => .ok ()
def model : (body : Body) → Signature body
 | .next => model_next
 | .back => model_back
 | .rev => model_rev
 | .into_iter => Result.ok
 | .reverse_new => fun range => .ok ⟨range⟩
 | .drop => fun _ => .ok ()
/-- Range's two usize fields and Rev's sole Range field have no user Drop.
The generated empty drop glue remains at V370 rather than a new trust item. -/
theorem range_links : PV_B3P_Link_std_dependency_closure14 Signature source model := by
 intro body
 cases body with
 | next => funext range; exact next_binding range
 | back => funext range; exact back_binding range
 | rev => funext reverse; exact rev_binding reverse
 | into_iter => rfl
 | reverse_new => rfl
 | drop => rfl
#print axioms next_binding
#print axioms back_binding
#print axioms rev_binding
#print axioms forward_precondition
#print axioms backward_precondition
#print axioms backward_value
#print axioms range_links
end PV_B3Q_Range
