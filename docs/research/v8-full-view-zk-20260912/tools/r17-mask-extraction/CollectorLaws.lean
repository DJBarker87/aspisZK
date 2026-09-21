import AspisR17MaskSource.IteratorCompat

open Aeneas Aeneas.Std Result Lean.Order
namespace AspisR17MaskSource.IteratorCompat

def observe {A S : Type} (r : Result (A × S)) : Result A := do
  let (value, _) ← r
  ok value

private def Approx {A : Type} (x y : Result A) : Prop := x = div ∨ x = y

private theorem collectListState_below {I B : Type}
    (it : core.iter.traits.iterator.Iterator I B) :
    ∀ iter acc, Approx (observe (collectListState it iter acc))
      (alloc.vec.FromIteratorVec.iterToList it iter acc) := by
  apply collectListState.fixpoint_induct it
    (motive := fun f => ∀ iter acc, Approx (observe (f iter acc))
      (alloc.vec.FromIteratorVec.iterToList it iter acc))
  · apply admissible_pi_apply (fun (iter : I) (f : List B → Result (List B × I)) => ∀ acc,
      Approx (observe (f acc)) (alloc.vec.FromIteratorVec.iterToList it iter acc))
    intro iter
    apply admissible_pi_apply (fun (acc : List B) (r : Result (List B × I)) =>
      Approx (observe r) (alloc.vec.FromIteratorVec.iterToList it iter acc))
    intro acc
    exact admissible_flatOrder _ (Or.inl rfl)
  · intro f ih iter acc
    rw [alloc.vec.FromIteratorVec.iterToList.eq_1]
    cases hn : it.next iter with
    | fail e => simp [Approx, observe, hn]
    | div => simp [Approx, observe, hn]
    | ok result =>
      rcases result with ⟨value, next⟩
      cases value with
      | none => simp [Approx, observe, hn]
      | some value => simpa only [hn, bind_tc_ok] using ih next (value :: acc)

private theorem iterToList_below {I B : Type}
    (it : core.iter.traits.iterator.Iterator I B) :
    ∀ iter acc, Approx (alloc.vec.FromIteratorVec.iterToList it iter acc)
      (observe (collectListState it iter acc)) := by
  apply alloc.vec.FromIteratorVec.iterToList.fixpoint_induct it
    (motive := fun f => ∀ iter acc, Approx (f iter acc)
      (observe (collectListState it iter acc)))
  · apply admissible_pi_apply (fun (iter : I) (f : List B → Result (List B)) => ∀ acc,
      Approx (f acc) (observe (collectListState it iter acc)))
    intro iter
    apply admissible_pi_apply (fun (acc : List B) (r : Result (List B)) =>
      Approx r (observe (collectListState it iter acc)))
    intro acc
    exact admissible_flatOrder _ (Or.inl rfl)
  · intro f ih iter acc
    rw [collectListState.eq_1]
    cases hn : it.next iter with
    | fail e => simp [Approx, observe, hn]
    | div => simp [Approx, observe, hn]
    | ok result =>
      rcases result with ⟨value, next⟩
      cases value with
      | none => simp [Approx, observe, hn]
      | some value => simpa only [hn, bind_tc_ok] using ih next (value :: acc)

/-- Unconditional equality, not just equality on terminating successes:
the added final state does not alter list values, errors or divergence. -/
theorem collectListState_observe {I B : Type}
    (it : core.iter.traits.iterator.Iterator I B) (iter : I) (acc : List B) :
    observe (collectListState it iter acc) =
      alloc.vec.FromIteratorVec.iterToList it iter acc := by
  rcases collectListState_below it iter acc with hd | he
  · rcases iterToList_below it iter acc with hd' | he'
    · exact hd.trans hd'.symm
    · exact he'.symm
  · exact he

/-- The state-retaining vector collector has exactly the cached collector's
observable Result, including its length check. No termination hypothesis. -/
theorem collectState_observe {I B : Type}
    (it : core.iter.traits.iterator.Iterator I B) (iter : I) :
    observe (collectState it iter) =
      core.iter.traits.iterator.Iterator.collect.default it
        (core.iter.traits.collect.FromIteratorVec B) iter := by
  have h := collectListState_observe it iter []
  simp only [core.iter.traits.iterator.Iterator.collect.default,
    alloc.vec.FromIteratorVec.from_iter,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_tc_ok]
  cases hc : collectListState it iter [] with
  | fail e =>
    simp [observe, hc] at h
    simp [collectState, observe, hc, ← h]
  | div =>
    simp [observe, hc] at h
    simp [collectState, observe, hc, ← h]
  | ok result =>
    rcases result with ⟨values, finalIter⟩
    simp [observe, hc] at h
    simp only [collectState, hc, bind_tc_ok, ← h]
    by_cases hl : values.length ≤ Usize.max <;> simp [observe, hl]

#print axioms collectListState_observe
#print axioms collectState_observe

end AspisR17MaskSource.IteratorCompat
