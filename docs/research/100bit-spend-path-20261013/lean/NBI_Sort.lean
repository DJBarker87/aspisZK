import NBI_Keys
import MultiproofConeSortStep
import Port4B_SortInstall

set_option autoImplicit false
namespace AspisR1.NBI_Sort
open Aeneas Aeneas.Std Result MultiproofSortRef
open MultiproofConeSortStep

/-- Natural carrier of NBE's ONE native swap/stop check. No sorted output
or whole-sort equation is included in the observation. -/
def NativeStep (keys : Array U64 16#usize) (cursor : Usize) :
    sort_reference.InsertStep → Prop
  | .Done out => out = keys ∧ (cursor.val = 0 ∨
      keys.val[cursor.val-1]!.val ≤ keys.val[cursor.val]!.val)
  | .Next out lower => lower.val+1 = cursor.val ∧
      keys.val[lower.val]!.val > keys.val[cursor.val]!.val ∧
      out = (keys.set lower keys.val[cursor.val]!).set cursor keys.val[lower.val]!

/-- Single-step natural comparisons have the same meaning on the installed
U64 carrier; no modulo, truncated comparison or tie-order change is added. -/
theorem natural_post (keys : Array U64 16#usize) (cursor : Usize)
    (out : sort_reference.InsertStep) : NativeStep keys cursor out ↔ StepPost keys cursor out := by
  cases out <;> rfl

/-- A deterministic one-step observation uniquely selects the installed
step, including the zero cursor and equal-key stop cases. -/
theorem step_port (keys : Array U64 16#usize) (cursor : Usize) (bound : cursor.val < 16)
    (observed : sort_reference.InsertStep) (native : NativeStep keys cursor observed) :
    sort_reference.insert_step keys cursor = ok observed := by
  obtain ⟨actual,returned,post⟩ := insert_step_total keys cursor bound
  have obs := (natural_post keys cursor observed).mp native
  suffices actual = observed by simpa only [this] using returned
  cases actual with
  | Done out =>
    rcases post with ⟨rfl,stop⟩
    cases observed with
    | Done other => exact congrArg sort_reference.InsertStep.Done obs.1.symm
    | Next other lower =>
      rcases obs with ⟨lv,greater,eq⟩
      have same : lower.val = cursor.val-1 := by omega
      rcases stop with zero|le
      · omega
      · rw [same] at greater
        exact False.elim (not_lt_of_ge le greater)
  | Next out lower =>
    rcases post with ⟨lv,greater,rfl⟩
    cases observed with
    | Done other =>
      rcases obs.2 with zero|le
      · omega
      · have same : lower.val = cursor.val-1 := by omega
        rw [same] at greater
        exact False.elim (not_lt_of_ge le greater)
    | Next other otherLower =>
      rcases obs with ⟨ov,_,rfl⟩
      have same : lower = otherLower := UScalar.eq_of_val_eq (by omega)
      subst otherLower
      rfl

#print axioms natural_post
#print axioms step_port
end AspisR1.NBI_Sort
