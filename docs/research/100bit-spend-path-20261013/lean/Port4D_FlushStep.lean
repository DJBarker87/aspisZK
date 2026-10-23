import Port4D_FlushABI
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4D_FlushABI
open Aeneas Aeneas.Std Result ControlFlow
def iteratorWriteBack (offset : Nat) (it : FinishIterMut)
    (replacement : Option K) : FinishIterMut :=
  match replacement with
  | none => it
  | some value => { it with slice := it.slice.setAtNat offset value }

def some_step_law (eval : Usize → Result K) (total : Nat)
    (f : Nat → K) : Prop :=
  ∀ iter : FinishIter, iter.iter.i < total → iter.count.val = iter.iter.i →
    (iter.iter.slice.len).val = total →
    ∃ index x iter1 nextBack,
      next iter =
        .ok (some (index, x), iter1, nextBack) ∧
      index.val = iter.iter.i ∧ iter1.iter.i = iter.iter.i + 1 ∧
      iter1.iter.slice = iter.iter.slice ∧ iter1.count.val = iter.iter.i + 1 ∧
      eval index = .ok (f index.val) ∧
      (∀ e : FinishIter,
        (nextBack e (some (index, f index.val))).iter.slice =
          e.iter.slice.setAtNat iter.iter.i (f iter.iter.i))

def none_step_law (total : Nat) : Prop :=
  ∀ iter : FinishIter, total ≤ iter.iter.i →
    (iter.iter.slice.len).val = total →
    ∃ iter1 nextBack,
      next iter =
        .ok (none, iter1, nextBack) ∧ iter1.iter.i = iter.iter.i ∧
      iter1.iter.slice = iter.iter.slice ∧
      (∀ e : FinishIter, (nextBack e none).iter.slice = e.iter.slice)

theorem some_step_law_actual (eval : Usize → Result K) (total : Nat)
    (f : Nat → K)
    (hcapacity : total ≤ Std.Usize.max)
    (hvalue : ∀ i : Std.Usize, i.val < total →
      eval i = .ok (f i.val)) :
    some_step_law eval total f := by
  intro iter hlt hc hlen
  have hwithin : iter.iter.i < (iter.iter.slice.len).val := by simpa [hlen] using hlt
  have hroom : iter.count.val + 1 ≤ Std.Usize.max := by
    rw [hc]
    omega
  have haddSpec : UScalar.add iter.count 1#usize
      ⦃z => z.val = iter.count.val + 1⦄ := by
    apply UScalar.add_spec
    have hsum : iter.count.val + (1#usize).val ≤ Std.Usize.max := by simpa using hroom
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨countNext, hadd, hcountNextRaw⟩ := WP.spec_imp_exists haddSpec
  have hcountNext : countNext.val = iter.iter.i + 1 := by simpa [hc] using hcountNextRaw
  let index := iter.count
  let value := iter.iter.slice[iter.iter.i]
  let iter1 : FinishIter := { iter with
    iter := { iter.iter with i := iter.iter.i + 1 }, count := countNext }
  let nextBack : FinishNextBack := fun current replacement =>
    { current with iter := iteratorWriteBack iter.iter.i current.iter (replacement.map Prod.snd) }
  have hindex : index.val = iter.iter.i := hc
  let mutNext : FinishIterMut := { iter.iter with i := iter.iter.i + 1 }
  let rawWriteBack : FinishIterMut → Option K → FinishIterMut :=
    fun current replacement => iteratorWriteBack iter.iter.i current replacement
  have hnextMut : core.slice.iter.IteratorIterMut.next iter.iter =
      .ok (some value, mutNext, rawWriteBack) := by
    unfold core.slice.iter.IteratorIterMut.next
    rw [dif_pos hwithin]
    simp [value, mutNext, rawWriteBack, iteratorWriteBack]
    funext it' replacement
    cases replacement <;> rfl
  have haddNotation : (iter.count + 1#usize : Result Std.Usize) = .ok countNext := by
    change UScalar.add iter.count 1#usize = .ok countNext
    exact hadd
  have hnext : next iter =
      .ok (some (index, value), iter1, nextBack) := by
    unfold next
    rw [hnextMut]
    rw [haddNotation]
    simp [index, iter1, nextBack, rawWriteBack, iteratorWriteBack, mutNext]
  have hval : eval index = .ok (f index.val) := by
    exact hvalue index (by simpa [hindex] using hlt)
  refine ⟨index, value, iter1, nextBack, hnext, hindex, ?_, ?_, ?_, hval, ?_⟩
  · rfl
  · rfl
  · change countNext.val = iter.iter.i + 1
    exact hcountNext
  · intro e
    simp [nextBack, iteratorWriteBack, hindex]

theorem none_step_law_actual (total : Nat) : none_step_law total := by
  intro iter hdone hlen
  have hnot : ¬ iter.iter.i < (iter.iter.slice.len).val := by
    rw [hlen]
    omega
  let nextBack : FinishNextBack := fun current _ => current
  have hnextMut : core.slice.iter.IteratorIterMut.next iter.iter =
      .ok (none, iter.iter, fun current _ => current) := by
    unfold core.slice.iter.IteratorIterMut.next
    rw [dif_neg hnot]
  refine ⟨iter, nextBack, ?_, rfl, rfl, ?_⟩
  · unfold next
    rw [hnextMut]
    simp [nextBack]
  · intro e
    rfl


#print axioms some_step_law_actual
#print axioms none_step_law_actual
end AspisR1.Port4D_FlushABI
end
