import AspisR1BatchedWeightsFinishExtraction.BatchedWeightsFinishGenerated
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1BatchedWeightsFinishExtraction
namespace EnumerateMutCorrespondence

abbrev MutableEnumerator (T : Type) :=
  core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut T)

abbrev MutableNextResult (T : Type) :=
  Result ((Option (Std.Usize × T)) × MutableEnumerator T ×
    (MutableEnumerator T → Option (Std.Usize × T) → MutableEnumerator T))

/-- Forgetting the Aeneas mutable write-back continuation projects the custom
`nextWithBack` step to the ordinary generic Enumerate `next` step. -/
def forgetBack {T : Type} (r : MutableNextResult T) :
    Result ((Option (Std.Usize × T)) × MutableEnumerator T) := do
  let (item, state, _) ← r
  ok (item, state)

theorem nextWithBack_projects_to_generic_enumerate_next
    {T : Type} (state : MutableEnumerator T) :
    forgetBack (core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack state) =
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT T) state := by
  simp only [forgetBack,
    core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack,
    core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorIterMut.nextForward]
  cases hnext : core.slice.iter.IteratorIterMut.next state.iter with
  | ok result =>
      rcases result with ⟨value, iter, back⟩
      cases value <;> simp [hnext, bind_tc_ok]
  | fail e => simp [hnext, bind_tc_fail]
  | div => simp [hnext, bind_tc_div]


/-- A successful mutable enumerate step carries precisely the inner iterator
back callback. The callback is threaded unchanged for `None`; for `Some`, an
optional replacement's value is sent to the inner slice write-back function. -/
theorem nextWithBack_success_routes_inner_callback
    {T : Type} (state : MutableEnumerator T)
    {item : Option (Std.Usize × T)} {state' : MutableEnumerator T}
    {back : MutableEnumerator T → Option (Std.Usize × T) → MutableEnumerator T}
    (h : core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack state =
      .ok (item, state', back)) :
    ∃ innerBack,
      core.slice.iter.IteratorIterMut.next state.iter =
        .ok (item.map Prod.snd, state'.iter, innerBack) ∧
      ∀ current replacement,
        back current replacement =
          { current with iter := (innerBack current.iter
            (if item.isSome then replacement.map Prod.snd else none)) } := by
  unfold core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack at h
  cases hnext : core.slice.iter.IteratorIterMut.next state.iter with
  | fail e => simp [hnext, bind_tc_fail] at h
  | div => simp [hnext, bind_tc_div] at h
  | ok res =>
      rcases res with ⟨value, iter, innerBack⟩
      rw [hnext] at h
      cases value with
      | none =>
          simp only [bind_tc_ok] at h
          have hout := Result.ok.inj h
          have hitem : none = item := congrArg Prod.fst hout
          have htail := congrArg Prod.snd hout
          have hstate : { iter := iter, count := state.count } = state' := congrArg Prod.fst htail
          have hback : (fun current _ => { current with iter := innerBack current.iter none }) = back := congrArg Prod.snd htail
          subst item
          subst state'
          subst back
          exact ⟨innerBack, by simp [hnext], by intro current replacement; rfl⟩
      | some value =>
          change (do
            let count ← state.count + 1#usize
            ok (some (state.count, value), ({ iter := iter, count } : MutableEnumerator T),
              fun (current : MutableEnumerator T)
                  (replacement : Option (Std.Usize × T)) =>
                { current with iter := innerBack current.iter (replacement.map Prod.snd) })) =
              .ok (item, state', back) at h
          cases hcount : state.count + 1#usize with
          | fail e => simp [hcount, bind_tc_fail] at h
          | div => simp [hcount, bind_tc_div] at h
          | ok count =>
              rw [hcount] at h
              simp only [bind_tc_ok] at h
              have hout := Result.ok.inj h
              have hitem : some (state.count, value) = item := congrArg Prod.fst hout
              have htail := congrArg Prod.snd hout
              have hstate : { iter := iter, count := count } = state' := congrArg Prod.fst htail
              have hback : (fun current replacement =>
                { current with iter := innerBack current.iter (replacement.map Prod.snd) }) = back := congrArg Prod.snd htail
              subst item
              subst state'
              subst back
              exact ⟨innerBack, by simp [hnext], by intro current replacement; rfl⟩

#print axioms nextWithBack_success_routes_inner_callback

#print axioms nextWithBack_projects_to_generic_enumerate_next
end EnumerateMutCorrespondence
end AspisR1BatchedWeightsFinishExtraction
