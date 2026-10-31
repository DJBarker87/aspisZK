import PV_B3P_DirectRange17227
import PV_B3P_InclusiveCaller15227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std Result ControlFlow
open PV_B3P_Binding11227 PV_B3P_Binding13227
set_option autoImplicit false

theorem inclusive_next_extraction17 (first last : Usize) (exhausted : Bool) :
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize ⟨first,last,exhausted⟩ =
    if exhausted = true ∨ last.val < first.val then .ok (none,⟨first,last,exhausted⟩)
    else if first.val < last.val then
      .ok (some first,⟨Usize.wrapping_add first 1#usize,last,false⟩)
    else .ok (some first,⟨first,last,true⟩) := by
  obtain ⟨⟨item,rest⟩,execution,spec⟩ := WP.spec_imp_exists
    (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next_Usize_spec
      ⟨first,last,exhausted⟩)
  by_cases empty : exhausted = true ∨ last.val < first.val
  · simp only [empty,if_true] at spec
    rcases spec with ⟨item_eq,rest_eq⟩
    simp only [empty,if_true,execution,item_eq,rest_eq]
  · by_cases inside : first.val < last.val
    · simp only [empty,if_false,inside,if_true] at spec
      rcases spec with ⟨item_eq,start_val,end_eq,flag_eq⟩
      have order : first < last := by scalar_tac
      have add_val := PV_B3P_Offset226V3.add_value first 1#usize
        (range_increment_safe13 first last order)
      have start_eq : rest.start = Usize.wrapping_add first 1#usize := by scalar_tac
      have rest_eq : rest = ⟨Usize.wrapping_add first 1#usize,last,false⟩ := by
        cases rest
        simp_all
      simp only [empty,if_false,inside,if_true,execution,item_eq,rest_eq]
    · simp only [empty,if_false,inside] at spec
      rcases spec with ⟨item_eq,start_eq,end_eq,flag_eq⟩
      have rest_eq : rest = ⟨first,last,true⟩ := by cases rest; simp_all
      simp only [empty,if_false,inside,execution,item_eq,rest_eq]

def inclusive_std_body17 {α : Type} (step : α → Usize → Result α)
    (state : core.ops.range.RangeInclusive Usize × α) :
    Result (ControlFlow (core.ops.range.RangeInclusive Usize × α) α) := do
  let (item,iter) ← core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
    core.iter.range.StepUsize state.1
  match item with
  | none => .ok (.done state.2)
  | some index => do
    let next ← step state.2 index
    .ok (.cont (iter,next))

def inclusive_std_loop17 {α : Type} (step : α → Usize → Result α)
    (first last : Usize) (state : α) : Result α :=
  loop (inclusive_std_body17 step) (⟨first,last,false⟩,state)

theorem inclusive_exhausted17 {α : Type} (step : α → Usize → Result α)
    (first last : Usize) (state : α) :
    loop (inclusive_std_body17 step) (⟨first,last,true⟩,state) = .ok state := by
  rw [loop.eq_1]
  simp only [inclusive_std_body17,inclusive_next_extraction17,true_or,if_true,bind_tc_ok]

theorem inclusive_more17 (first last : Usize) (inside : first.val < last.val) :
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize ⟨first,last,false⟩ =
    .ok (some first,⟨Usize.wrapping_add first 1#usize,last,false⟩) := by
  have empty : ¬ (false = true ∨ last.val < first.val) := by simp only [Bool.false_eq_true,false_or]; omega
  simp only [inclusive_next_extraction17,empty,if_false,inside,if_true]

theorem inclusive_final17 (last : Usize) :
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize ⟨last,last,false⟩ = .ok (some last,⟨last,last,true⟩) := by
  simp only [inclusive_next_extraction17,Bool.false_eq_true,false_or,Nat.lt_irrefl,if_false]

theorem inclusive_std_fold17 {α : Type} (step : α → Usize → Result α)
    (last first : Usize) (limit : last.val < 24) (n : Nat) (state : α)
    (count : first.val+n=last.val+1) :
    inclusive_std_loop17 step first last state =
      PV_B3P_Ordered227.fold step (usize_indices11 n first) state := by
  induction n generalizing first state with
  | zero =>
    have empty : last.val < first.val := by omega
    unfold inclusive_std_loop17
    rw [loop.eq_1]
    simp only [inclusive_std_body17,inclusive_next_extraction17,empty,or_true,if_true,
      bind_tc_ok,usize_indices11,PV_B3P_Ordered227.fold]
  | succ n ih =>
    by_cases final : first = last
    · subst first
      have zero : n=0 := by omega
      subst n
      unfold inclusive_std_loop17
      rw [loop.eq_1]
      simp only [inclusive_std_body17,inclusive_final17,bind_tc_ok,inclusive_exhausted17,
        usize_indices11,PV_B3P_Ordered227.fold]
      cases operation : step state last <;> simp only [bind_tc_ok,inclusive_exhausted17]
    · have inside : first.val < last.val := by scalar_tac
      have inc := PV_B3P_Offset226V3.add_value first 1#usize
        (range_increment_safe13 first last (by scalar_tac))
      change (Usize.wrapping_add first 1#usize).val = first.val+1 at inc
      have rest : (Usize.wrapping_add first 1#usize).val+n=last.val+1 := by rw [inc]; omega
      unfold inclusive_std_loop17
      rw [loop.eq_1]
      simp only [inclusive_std_body17,inclusive_more17 first last inside,bind_tc_ok,
        usize_indices11,PV_B3P_Ordered227.fold]
      cases operation : step state first with
      | fail e => rfl
      | div => rfl
      | ok next =>
        simpa only [inclusive_std_loop17,bind_tc_ok] using
          (ih (Usize.wrapping_add first 1#usize) next rest)

#print axioms inclusive_next_extraction17
#print axioms inclusive_exhausted17
#print axioms inclusive_more17
#print axioms inclusive_final17
#print axioms inclusive_std_fold17
end PV_B3P_Direct17227
