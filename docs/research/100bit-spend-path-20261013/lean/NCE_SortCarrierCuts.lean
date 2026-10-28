import NCE_OpeningRead
import NBI_Sort

set_option autoImplicit false
namespace AspisR1.NCE_SortCarrierCuts
open Aeneas Aeneas.Std Result MultiproofSortRef NCE_OpeningCuts
abbrev Step := Carrier → Array U64 16#usize → Usize → Result (sort_reference.InsertStep × Carrier)

/-- Strengthened ONE-iteration native sort cut: the same natural swap/stop
law AND the actual unchanged Prepared/proof/scratch/log caller. The older
value-only Step signature cannot by itself provide this external frame. -/
def NCE_Native_KeysSortCarrier (native : Step) : Prop :=
  ∀ caller keys cursor, cursor.val < 16 → ∃ out,
    native caller keys cursor = ok (out,caller) ∧ NBI_Sort.NativeStep keys cursor out

def insert (native : Step) : Nat → Carrier → Array U64 16#usize → Usize → Result (Array U64 16#usize × Carrier)
  | 0,_,_,_ => .div
  | fuel+1,caller,keys,cursor => do
      let step ← native caller keys cursor
      match step.1 with
      | .Done finished => ok (finished,step.2)
      | .Next next lower => insert native fuel step.2 next lower

/-- Exact native insertion result plus caller frame from local sort cuts. -/
theorem insert_eq (native : Step) (cut : NCE_Native_KeysSortCarrier native)
    (fuel : Nat) (caller : Carrier) (keys : Array U64 16#usize) (cursor : Usize)
    (bound : cursor.val < 16) (enough : cursor.val < fuel) :
    insert native fuel caller keys cursor =
      (do let out ← sort_reference.insert_rows keys cursor; ok (out,caller)) := by
  induction fuel generalizing caller keys cursor with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨out,returned,post⟩ := cut caller keys cursor bound
    have source := NBI_Sort.step_port keys cursor bound out post
    rw [insert,returned,sort_reference.insert_rows,source]
    simp only [bind_tc_ok]
    cases out with
    | Done finished => rfl
    | Next next lower => exact ih caller next lower (by have := post.1; omega) (by have := post.1; omega)

def sort (native : Step) : Nat → Carrier → Array U64 16#usize → Usize → Usize → Result (Array U64 16#usize × Carrier)
  | 0,caller,keys,cursor,n => if cursor >= n then ok (keys,caller) else .div
  | fuel+1,caller,keys,cursor,n => do
      if cursor >= n then ok (keys,caller) else
      let inserted ← insert native (cursor.val+1) caller keys cursor
      let higher ← cursor+1#usize
      sort native fuel inserted.2 inserted.1 higher n

/-- Native outer sort consumes its actual insertion child return and caller.
No independent sorted array or final-frame equation is a premise. -/
theorem sort_eq (native : Step) (cut : NCE_Native_KeysSortCarrier native)
    (fuel : Nat) (caller : Carrier) (keys : Array U64 16#usize) (cursor n : Usize)
    (small : n.val ≤ 16) (enough : n.val-cursor.val ≤ fuel) :
    sort native fuel caller keys cursor n =
      (do let out ← sort_reference.sort_rows keys cursor n; ok (out,caller)) := by
  induction fuel generalizing caller keys cursor with
  | zero =>
    have halt : cursor >= n := by change cursor.val >= n.val; omega
    rw [sort,if_pos halt,sort_reference.sort_rows,if_pos halt]
    rfl
  | succ fuel ih =>
    by_cases halt : cursor >= n
    · rw [sort,if_pos halt,sort_reference.sort_rows,if_pos halt]
      rfl
    · have active : cursor.val < n.val := by change ¬cursor.val >= n.val at halt; omega
      have bound : cursor.val < 16 := by omega
      rw [sort,if_neg halt,insert_eq native cut _ caller keys cursor bound (by omega),
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
        apply ih caller next higher
        have one : (1#usize).val = 1 := rfl
        rw [one] at value
        omega

#print axioms insert_eq
#print axioms sort_eq
end AspisR1.NCE_SortCarrierCuts
