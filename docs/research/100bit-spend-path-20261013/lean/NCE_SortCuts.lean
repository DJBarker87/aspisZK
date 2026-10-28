import NBI_Sort
import NBJ_Keys

set_option autoImplicit false
namespace AspisR1.NCE_SortCuts
open Aeneas Aeneas.Std Result MultiproofSortRef

abbrev Step := Array U64 16#usize → Usize → Result sort_reference.InsertStep

/-- ONE native insertion comparison/swap/stop on arbitrary keys and cursor.
The existing natural postcondition includes the exact swapped cells and
outside frame; no sorted result or entire insertion run is a premise. -/
def NCE_Native_KeysSort (native : Step) : Prop :=
  ∀ keys cursor, cursor.val < 16 → ∃ out,
    native keys cursor = ok out ∧ NBI_Sort.NativeStep keys cursor out

/-- Reuse the existing unique local sort-step association. -/
theorem step_eq (native : Step) (cut : NCE_Native_KeysSort native)
    (keys : Array U64 16#usize) (cursor : Usize) (bound : cursor.val < 16) :
    native keys cursor = sort_reference.insert_step keys cursor := by
  obtain ⟨out,returned,post⟩ := cut keys cursor bound
  exact returned.trans (NBI_Sort.step_port keys cursor bound out post).symm

/-- Source-specific insertion continuation. Native verification targets only
its one comparison/swap body; Lean handles the strictly decreasing cursor. -/
def insert (native : Step) : Nat → Array U64 16#usize → Usize → Result (Array U64 16#usize)
  | 0,_,_ => .div
  | fuel+1,keys,cursor => do
      let out ← native keys cursor
      match out with
      | .Done finished => ok finished
      | .Next next lower => insert native fuel next lower

/-- Native one-step cuts compose to the actual emitted insertion function.
The recursive native call consumes the immediately preceding keys/cursor. -/
theorem insert_eq (native : Step) (cut : NCE_Native_KeysSort native)
    (fuel : Nat) (keys : Array U64 16#usize) (cursor : Usize)
    (bound : cursor.val < 16) (enough : cursor.val < fuel) :
    insert native fuel keys cursor = sort_reference.insert_rows keys cursor := by
  induction fuel generalizing keys cursor with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨out,returned,post⟩ := cut keys cursor bound
    have source := NBI_Sort.step_port keys cursor bound out post
    rw [insert,returned,sort_reference.insert_rows,source]
    simp only [bind_tc_ok]
    cases out with
    | Done finished => rfl
    | Next next lower =>
      have advance := post.1
      exact ih next lower (by omega) (by omega)

/-- Native outer for-loop control is represented in source order, with the
closed conditional insertion result as its actual child, never a free sorted
array. Its separate native dispatch/add association is still required. -/
def sort (native : Step) : Nat → Array U64 16#usize → Usize → Usize → Result (Array U64 16#usize)
  | 0,keys,cursor,n => if cursor >= n then ok keys else .div
  | fuel+1,keys,cursor,n => do
      if cursor >= n then ok keys else
      let next ← insert native (cursor.val+1) keys cursor
      let higher ← cursor+1#usize
      sort native fuel next higher n

/-- The exact emitted full sort follows by outer induction; no final-sort
observation is assumed. Fuel only bounds the remaining native for-loop. -/
theorem sort_eq (native : Step) (cut : NCE_Native_KeysSort native)
    (fuel : Nat) (keys : Array U64 16#usize) (cursor n : Usize)
    (small : n.val ≤ 16) (enough : n.val-cursor.val ≤ fuel) :
    sort native fuel keys cursor n = sort_reference.sort_rows keys cursor n := by
  induction fuel generalizing keys cursor with
  | zero =>
    have halt : cursor >= n := by change cursor.val >= n.val; omega
    rw [sort,if_pos halt,sort_reference.sort_rows,if_pos halt]
  | succ fuel ih =>
    by_cases halt : cursor >= n
    · rw [sort,if_pos halt,sort_reference.sort_rows,if_pos halt]
    · have active : cursor.val < n.val := by change ¬cursor.val >= n.val at halt; omega
      have bound : cursor.val < 16 := by omega
      rw [sort,if_neg halt,insert_eq native cut _ keys cursor bound (by omega),
        sort_reference.sort_rows,if_neg halt]
      generalize inserted : sort_reference.insert_rows keys cursor = out
      cases out with
      | fail e => rfl
      | div => rfl
      | ok next =>
        simp only [bind_tc_ok]
        obtain ⟨higher,add,value⟩ := WP.spec_imp_exists
          (UScalar.add_spec (x:=cursor) (y:=1#usize) (by scalar_tac))
        rw [add]
        simp only [bind_tc_ok]
        apply ih next higher
        have one : (1#usize).val = 1 := rfl
        rw [one] at value
        omega

#print axioms step_eq
#print axioms insert_eq
#print axioms sort_eq
end AspisR1.NCE_SortCuts
