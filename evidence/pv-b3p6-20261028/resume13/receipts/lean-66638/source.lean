import PV_B3P_SliceIter13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_Binding9227 Result ControlFlow
set_option autoImplicit false
/-- Forward enumerate(iter_mut) with the write/restoration continuation kept as
step, and both iterator fields retained in the loop state. -/
def slice_body13 {α : Type} (step : α → Usize → Result α)
    (state : α × Usize × Usize) : Result (ControlFlow (α × Usize × Usize) α) := do
  let (item,index,count) ← enumerate_next13 state.2.1 state.2.2
  match item with
  | none =>
    let _ ← slice_iterator_drop13 index count
    .ok (.done state.1)
  | some (group,_slot) =>
    let next ← step state.1 group
    .ok (.cont (next,index,count))

def slice_loop13 {α : Type} (step : α → Usize → Result α)
    (state : α) : Result α := loop (slice_body13 step) (state,0#usize,0#usize)

theorem slice_loop_plan13 {α : Type} (step : α → Usize → Result α)
    (n : Nat) (index : Usize) (state : α) (bound : index.val+n=4) :
    loop (slice_body13 step) (state,index,index) = usize_plan step n index state := by
  induction n generalizing index state with
  | zero =>
    have end_index : index = 4#usize := by scalar_tac
    subst index
    rw [loop.eq_1]
    simp only [slice_body13,enumerate_finish13,bind_tc_ok,slice_iterator_drop13,usize_plan]
  | succ n ih =>
    have small : index.val < 4 := by omega
    have next : (Usize.wrapping_add index 1#usize).val = index.val+1 := cursor_increment13 index small
    rw [loop.eq_1]
    simp only [slice_body13,enumerate_step13 index small,bind_tc_ok,usize_plan]
    cases hs : step state index with
    | fail e => rfl
    | div => rfl
    | ok state1 =>
      simp only [bind_tc_ok]
      exact ih _ state1 (by omega)

theorem slice_loop_four13 {α : Type} (step : α → Usize → Result α) (state : α) :
    slice_loop13 step state = usize_plan step 4 0#usize state :=
  slice_loop_plan13 step 4 0#usize state (by rfl)
#print axioms slice_loop_plan13
#print axioms slice_loop_four13
end PV_B3P_Binding13227
