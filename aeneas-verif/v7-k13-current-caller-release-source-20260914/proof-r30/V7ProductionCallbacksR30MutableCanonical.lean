import V7ProductionCallbacksR30KaratsubaCanonical

/-! Generic predicate preservation for the exact mutable enumerate adapter. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000
open Aeneas Aeneas.Std Result ControlFlow Error

namespace V7ProductionCallbacksR30MutableCanonical

abbrev Enum (T : Type) := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)

def SliceAll {T : Type} [Inhabited T] (P : T → Prop) (slice : Slice T) : Prop :=
  ∀ index, index < slice.length → P slice.val[index]!

def BackAll {T : Type} [Inhabited T] (P : T → Prop) (back : Enum T → Enum T) : Prop :=
  ∀ candidate, SliceAll P candidate.iter.slice → SliceAll P (back candidate).iter.slice

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do let value ← input; next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

theorem slice_set_all {T : Type} [Inhabited T]
    (P : T → Prop) (slice : Slice T) (position : Nat) (value : T)
    (canonical : SliceAll P slice) (valueCanonical : P value) :
    SliceAll P (slice.setAtNat position value) := by
  intro target bound
  have oldBound : target < slice.length := by simpa [Slice.setAtNat] using bound
  by_cases same : target = position
  · subst target
    simpa [Slice.setAtNat, List.getElem!_eq_getElem?_getD, oldBound] using valueCanonical
  · have oldCanonical := canonical target oldBound
    simpa [Slice.setAtNat, List.getElem!_eq_getElem?_getD, same] using oldCanonical

theorem enumerate_some_all {T : Type} [Inhabited T]
    (P : T → Prop) (state next : Enum T)
    (nextBack : Enum T → Option (Std.Usize × T) → Enum T)
    (slot : Std.Usize) (oldValue : T)
    (run : core.iter.adapters.enumerate.IteratorEnumerateMut.next state =
      ok (some (slot, oldValue), next, nextBack))
    (canonical : SliceAll P state.iter.slice) :
    P oldValue ∧ SliceAll P next.iter.slice ∧
      ∀ value, P value → BackAll P (fun candidate => nextBack candidate (some (slot, value))) := by
  unfold core.iter.adapters.enumerate.IteratorEnumerateMut.next
    core.slice.iter.IteratorIterMut.next at run
  split at run
  · rename_i active
    simp only [bind_tc_ok] at run
    rw [bind_eq_ok_iff] at run
    obtain ⟨nextCount, countRun, run⟩ := run
    simp only [Result.ok.injEq, Prod.mk.injEq, Option.some.injEq] at run
    obtain ⟨⟨slotExact, valueExact⟩, nextExact, backExact⟩ := run
    have oldCanonical := canonical state.iter.i (by exact active)
    have valueAt : oldValue = state.iter.slice.val[state.iter.i]! := by
      rw [← List.Inhabited_getElem_eq_getElem! state.iter.slice.val state.iter.i active]
      exact valueExact.symm
    refine ⟨valueAt ▸ oldCanonical, ?_, ?_⟩
    · rw [← nextExact]
      exact canonical
    · intro value valueCanonical candidate candidateCanonical
      rw [← backExact]
      exact slice_set_all P candidate.iter.slice state.iter.i value candidateCanonical valueCanonical
  · simp [Bind.bind, Aeneas.Std.bind] at run

theorem enumerate_none_all {T : Type} [Inhabited T]
    (P : T → Prop) (state next : Enum T)
    (nextBack : Enum T → Option (Std.Usize × T) → Enum T)
    (run : core.iter.adapters.enumerate.IteratorEnumerateMut.next state =
      ok (none, next, nextBack))
    (canonical : SliceAll P state.iter.slice) :
    SliceAll P (nextBack next none).iter.slice := by
  unfold core.iter.adapters.enumerate.IteratorEnumerateMut.next
    core.slice.iter.IteratorIterMut.next at run
  split at run
  · simp only [bind_tc_ok] at run
    rw [bind_eq_ok_iff] at run
    obtain ⟨nextCount, _, run⟩ := run
    cases run
  · simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨_, nextExact, backExact⟩ := run
    rw [← nextExact, ← backExact]
    exact canonical

#print axioms enumerate_some_all
#print axioms enumerate_none_all

theorem enumerate_none_back_all {T : Type} [Inhabited T]
    (P : T → Prop) (state next : Enum T)
    (nextBack : Enum T → Option (Std.Usize × T) → Enum T)
    (run : core.iter.adapters.enumerate.IteratorEnumerateMut.next state =
      ok (none, next, nextBack)) :
    BackAll P (fun candidate => nextBack candidate none) := by
  unfold core.iter.adapters.enumerate.IteratorEnumerateMut.next
    core.slice.iter.IteratorIterMut.next at run
  split at run
  · simp only [bind_tc_ok] at run
    rw [bind_eq_ok_iff] at run
    obtain ⟨nextCount, _, run⟩ := run
    cases run
  · simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at run
    obtain ⟨_, _, backExact⟩ := run
    rw [← backExact]
    intro candidate canonical
    exact canonical

end V7ProductionCallbacksR30MutableCanonical
