import PV_B3P_SliceLoop13227
import PV_B3P_ArrayWrite227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_Binding9227 Result
set_option autoImplicit false
/-- The callback computes its new slot from immutable captures; it then calls
exactly the retained mutable-borrow restoration continuation. -/
def slice_store13 {α : Type} (compute : Usize → Result α)
    (output : Array α 4#usize) (index : Usize) : Result (Array α 4#usize) := do
  let (_old,back) ← Array.index_mut_usize output index
  let value ← compute index
  .ok (back value)

def index_store13 {α : Type} (compute : Usize → Result α)
    (output : Array α 4#usize) (index : Usize) : Result (Array α 4#usize) := do
  let value ← compute index
  Array.update output index value

theorem slot_store_binding13 {α : Type} (compute : Usize → Result α)
    (output : Array α 4#usize) (index : Usize) (bound : index.val < 4) :
    slice_store13 compute output index = index_store13 compute output index := by
  unfold slice_store13 index_store13
  rw [PV_B3P_ArrayWrite227.borrow output index bound]
  simp only [bind_tc_ok]
  cases h : compute index with
  | fail e => rfl
  | div => rfl
  | ok value =>
    simp only [bind_tc_ok]
    exact (PV_B3P_ArrayWrite227.update output index bound value).symm

theorem store_plan_binding13 {α : Type} (compute : Usize → Result α)
    (n : Nat) (index : Usize) (output : Array α 4#usize) (bound : index.val+n ≤ 4) :
    usize_plan (slice_store13 compute) n index output =
      usize_plan (index_store13 compute) n index output := by
  induction n generalizing index output with
  | zero => rfl
  | succ n ih =>
    have small : index.val < 4 := by omega
    have next := cursor_increment13 index small
    simp only [usize_plan,slot_store_binding13 compute output index small]
    cases h : index_store13 compute output index with
    | fail e => rfl
    | div => rfl
    | ok state =>
      simp only [bind_tc_ok]
      exact ih _ state (by omega)

theorem iter_mut_restoration13 {α : Type} (compute : Usize → Result α)
    (output : Array α 4#usize) :
    slice_loop13 (slice_store13 compute) output =
      usize_plan (index_store13 compute) 4 0#usize output := by
  rw [slice_loop_four13]
  exact store_plan_binding13 compute 4 0#usize output (by rfl)
#print axioms slot_store_binding13
#print axioms store_plan_binding13
#print axioms iter_mut_restoration13
end PV_B3P_Binding13227
