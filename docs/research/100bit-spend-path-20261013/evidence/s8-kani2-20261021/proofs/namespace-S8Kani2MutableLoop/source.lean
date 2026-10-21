import S8Kani2MutableSource
import S8Kani2MutableStep
import S8Kani2PendingWrite
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
namespace S8Kani2MutableExtraction
namespace batched_weights
abbrev FinishNextBack := FinishIter → Option (Std.Usize × aspis_core.field.QM31) → FinishIter
abbrev FinishIterMut := core.slice.iter.IterMut aspis_core.field.QM31

def iteratorWriteBack (offset : Nat) (it : FinishIterMut)
    (replacement : Option aspis_core.field.QM31) : FinishIterMut :=
  match replacement with
  | none => it
  | some value => { it with slice := it.slice.setAtNat offset value }

def some_step_law (self : BatchedWeights) (total : Nat)
    (f : Nat → aspis_core.field.QM31) : Prop :=
  ∀ iter : FinishIter, iter.iter.i < total → iter.count.val = iter.iter.i →
    (iter.iter.slice.len).val = total →
    ∃ index x iter1 nextBack,
      core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack iter =
        .ok (some (index, x), iter1, nextBack) ∧
      index.val = iter.iter.i ∧ iter1.iter.i = iter.iter.i + 1 ∧
      iter1.iter.slice = iter.iter.slice ∧ iter1.count.val = iter.iter.i + 1 ∧
      BatchedWeights.value self index = .ok (f index.val) ∧
      (∀ e : FinishIter,
        (nextBack e (some (index, f index.val))).iter.slice =
          e.iter.slice.setAtNat iter.iter.i (f iter.iter.i))

def none_step_law (total : Nat) : Prop :=
  ∀ iter : FinishIter, total ≤ iter.iter.i →
    (iter.iter.slice.len).val = total →
    ∃ iter1 nextBack,
      core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack iter =
        .ok (none, iter1, nextBack) ∧ iter1.iter.i = iter.iter.i ∧
      iter1.iter.slice = iter.iter.slice ∧
      (∀ e : FinishIter, (nextBack e none).iter.slice = e.iter.slice)

theorem finish_loop_output_invariant_of_step_laws
    (self : BatchedWeights) (initial : FinishIter)
    (f : Nat → aspis_core.field.QM31)
    (hstart : initial.iter.i ≤ (initial.iter.slice.len).val)
    (hcount : initial.count.val = initial.iter.i)
    (hsome : some_step_law self (initial.iter.slice.len).val f)
    (hnone : none_step_law (initial.iter.slice.len).val) :
    ∃ output : FinishIter,
      BatchedWeights.finish_loop initial (fun e => e) self = .ok output ∧
      output.iter.slice = prefixWrite f initial.iter.i
        (initial.iter.slice.len).val initial.iter.slice := by
  let total := (initial.iter.slice.len).val
  let body := fun s : FinishIter × FinishBack =>
    BatchedWeights.finish_loop.body self s.1 s.2
  have hwp : WP.spec (loop body (initial, fun e => e))
      (fun output : FinishIter =>
        output.iter.slice = prefixWrite f initial.iter.i total initial.iter.slice) := by
    refine loop.spec_decr_nat
      (fun s : FinishIter × FinishBack => total - s.1.iter.i)
      (fun s => initial.iter.i ≤ s.1.iter.i ∧ s.1.iter.i ≤ total ∧ s.1.iter.slice = initial.iter.slice ∧
        s.1.count.val = s.1.iter.i ∧
        BackPrefix f initial.iter.i s.1.iter.i s.2)
      (fun output : FinishIter =>
        output.iter.slice = prefixWrite f initial.iter.i total initial.iter.slice)
      body (initial, fun e => e) ?_ ?_
    · rintro ⟨iter, back⟩ ⟨hlo, hi, hs, hc, hb⟩
      by_cases hlt : iter.iter.i < total
      · obtain ⟨index, x, iter1, nextBack, hnext, hindex, hi1, hs1, hc1, hvalue, hwrite⟩ :=
          hsome iter hlt hc (by simpa using congrArg (fun sl : FinishSlice => sl.len.val) hs)
        have hvalue' : BatchedWeights.value self index = .ok (f index.val) := hvalue
        have hbody := finish_loop_body_some self iter back index x (f index.val)
          iter1 nextBack hnext hvalue'
        have hnextBack : BackPrefix f initial.iter.i (iter.iter.i + 1)
            (fun e => back (nextBack e (some (index, f index.val)))) :=
          backPrefix_step f initial.iter.i iter.iter.i back index nextBack hb hindex
            (by omega) (by intro e; simpa [hindex, hc] using hwrite e)
        have hinvNext : initial.iter.i ≤ iter1.iter.i ∧ iter1.iter.i ≤ total ∧
            iter1.iter.slice = initial.iter.slice ∧ iter1.count.val = iter1.iter.i ∧
            BackPrefix f initial.iter.i iter1.iter.i
              (fun e => back (nextBack e (some (index, f index.val)))) := by
          have hloNext : initial.iter.i ≤ iter1.iter.i := by rw [hi1]; exact Nat.le_succ_of_le hlo
          have hiNext : iter1.iter.i ≤ total := by rw [hi1]; exact Nat.succ_le_iff.mpr hlt
          have hcNext : iter1.count.val = iter1.iter.i := by rw [hi1]; exact hc1
          exact ⟨hloNext, hiNext, hs1.trans hs, hcNext,
            by simpa [hi1] using hnextBack⟩
        have hmeasure : total - iter1.iter.i < total - iter.iter.i := by omega
        simpa [body, hbody] using And.intro hinvNext hmeasure
      · obtain ⟨iter1, nextBack, hnext, hi1, hs1, hnoWrite⟩ :=
          hnone iter (by omega) (by simpa using congrArg (fun sl : FinishSlice => sl.len.val) hs)
        have hbody := finish_loop_body_none self iter back iter1 nextBack hnext
        have hieq : iter.iter.i = total := Nat.le_antisymm hi (Nat.le_of_not_gt hlt)
        have hOutputSlice : (back (nextBack iter1 none)).iter.slice =
            prefixWrite f initial.iter.i total initial.iter.slice := by
          have hbp := hb (nextBack iter1 none)
          rw [hnoWrite] at hbp
          rw [hs1] at hbp
          rw [hs] at hbp
          rw [hieq] at hbp
          exact hbp
        simpa [body, hbody] using hOutputSlice
    · exact ⟨le_rfl, hstart, rfl, hcount, backPrefix_id f initial.iter.i⟩
  obtain ⟨output, hrun, hout⟩ := WP.spec_imp_exists hwp
  refine ⟨output, ?_, hout⟩
  simpa [body, BatchedWeights.finish_loop] using hrun

theorem some_step_law_actual (self : BatchedWeights) (total : Nat)
    (f : Nat → aspis_core.field.QM31)
    (hcapacity : total ≤ Std.Usize.max)
    (hvalue : ∀ i : Std.Usize, i.val < total →
      BatchedWeights.value self i = .ok (f i.val)) :
    some_step_law self total f := by
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
  let rawWriteBack : FinishIterMut → Option aspis_core.field.QM31 → FinishIterMut :=
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
  have hnext : core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack iter =
      .ok (some (index, value), iter1, nextBack) := by
    unfold core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack
    rw [hnextMut]
    rw [haddNotation]
    simp [index, iter1, nextBack, rawWriteBack, iteratorWriteBack, mutNext]
  have hval : BatchedWeights.value self index = .ok (f index.val) := by
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
  · unfold core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack
    rw [hnextMut]
    simp [nextBack]
  · intro e
    rfl

theorem finish_loop_output_invariant_of_values
    (self : BatchedWeights) (initial : FinishIter)
    (f : Nat → aspis_core.field.QM31)
    (hstart : initial.iter.i ≤ (initial.iter.slice.len).val)
    (hcount : initial.count.val = initial.iter.i)
    (hvalue : ∀ i : Std.Usize, i.val < (initial.iter.slice.len).val →
      BatchedWeights.value self i = .ok (f i.val))
    (hcapacity : (initial.iter.slice.len).val ≤ Std.Usize.max) :
    ∃ output : FinishIter,
      BatchedWeights.finish_loop initial (fun e => e) self = .ok output ∧
      output.iter.slice = prefixWrite f initial.iter.i
        (initial.iter.slice.len).val initial.iter.slice := by
  apply finish_loop_output_invariant_of_step_laws self initial f hstart hcount
  · exact some_step_law_actual self _ f hcapacity hvalue
  · exact none_step_law_actual _


#print axioms finish_loop_output_invariant_of_step_laws
#print axioms finish_loop_output_invariant_of_values
#print axioms some_step_law_actual

#print axioms none_step_law_actual

end batched_weights
end S8Kani2MutableExtraction
