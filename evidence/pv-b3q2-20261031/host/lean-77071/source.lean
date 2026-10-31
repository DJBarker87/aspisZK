import Aeneas.Std.RangeIter
import PV_B3Q_Range
namespace PV_B3Q_RangeActual
open Aeneas Aeneas.Std PV_B3P_Groups14227 core.ops.range
set_option autoImplicit false
def source (range : Range Usize) : Result (Option Usize × Range Usize) :=
 if range.start < range.end then
  .ok (some range.start,{range with start := Usize.wrapping_add range.start 1#usize})
 else .ok (none,range)
def model := core.iter.range.IteratorRange.next core.iter.range.StepUsize

theorem increment_safe (range : Range Usize) (guard : range.start < range.end) :
 range.start.val+1 < UScalar.size .Usize :=
 PV_B3P_Binding13227.range_increment_safe13 range.start range.end guard

theorem binding (range : Range Usize) : source range = model range := by
 have clone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by intro x; rfl
 have lt_ : ∀ x y : Usize, core.cmp.PartialOrdUsize.lt x y = .ok (decide (x.val < y.val)) := by
  intro x y
  rfl
 by_cases h : range.start.val < range.end.val
 · obtain ⟨⟨item,next⟩,run,post⟩ := WP.spec_imp_exists
     (core.iter.range.IteratorRange.next_UScalar_some_spec clone lt_ range h)
   change item = some range.start ∧ next.start.val = range.start.val+1 ∧ next.end=range.end at post
   have wrap : (Usize.wrapping_add range.start 1#usize).val = range.start.val+1 := by
    rw [Usize.wrapping_add_val_eq]
    exact Nat.mod_eq_of_lt (increment_safe range h)
   have startSame := UScalar.eq_of_val_eq (post.2.1.trans wrap.symm)
   have nextSame : next = {range with start := Usize.wrapping_add range.start 1#usize} := by
    cases next
    cases range
    simp_all
   change model range = .ok (item,next) at run
   rw [run]
   simp only [source,h,if_pos]
   rw [post.1,nextSame]
 · obtain ⟨⟨item,next⟩,run,post⟩ := WP.spec_imp_exists
     (core.iter.range.IteratorRange.next_UScalar_none_spec lt_ range (by omega))
   change item=none ∧ next=range at post
   change model range = .ok (item,next) at run
   rw [run]
   simp only [source,h,if_neg]
   rw [post.1,post.2]

theorem actual_range_link : PV_B3P_Link_std_dependency_closure14
 (fun _ : Unit => Range Usize → Result (Option Usize × Range Usize))
 (fun _ => source) (fun _ => model) := by
 intro _
 funext r
 exact binding r
#print axioms increment_safe
#print axioms binding
#print axioms actual_range_link
end PV_B3Q_RangeActual
