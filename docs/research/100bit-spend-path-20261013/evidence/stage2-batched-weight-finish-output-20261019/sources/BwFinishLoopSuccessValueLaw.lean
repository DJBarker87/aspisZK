import AspisR1BatchedWeightsFinishExtraction.BatchedWeightsFinishGenerated
import BwFinishBodySuccessInversion
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP

namespace AspisR1BatchedWeightsFinishExtraction
namespace batched_weights
namespace LoopSuccessValueLaw

abbrev FinishIter := core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut aspis_core.field.QM31)
abbrev FinishBack := FinishIter → FinishIter
abbrev FinishNextBack := FinishIter →
  Option (Std.Usize × aspis_core.field.QM31) → FinishIter
abbrev FinishBW := BatchedWeights
abbrev FinishQM := aspis_core.field.QM31

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem loop_success_cases {α β : Type} (step : α → Result (ControlFlow α β))
    (state : α) (out : β) (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧
        Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok cf =>
      cases cf with
      | done result =>
          simp [hs] at h
          subst result
          exact Or.inl rfl
      | cont stateNext =>
          simp [hs] at h
          exact Or.inr ⟨stateNext, rfl, h⟩

private theorem next_some_of_active
    (iter : FinishIter) (total : Nat)
    (hactive : iter.iter.i < total)
    (hlen : iter.iter.slice.len.val = total)
    (hcount : iter.count.val = iter.iter.i)
    (hcapacity : total ≤ Std.Usize.max) :
    ∃ index x iter1 nextBack,
      core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack iter =
        .ok (some (index, x), iter1, nextBack) ∧
      index.val = iter.count.val ∧
      iter1.count.val = iter.count.val + 1 ∧
      iter1.iter.i = iter.iter.i + 1 ∧
      iter1.iter.slice = iter.iter.slice := by
  have hwithin : iter.iter.i < iter.iter.slice.len.val := by omega
  have hroom : iter.count.val + 1 ≤ Std.Usize.max := by
    rw [hcount]
    omega
  have haddSpec : UScalar.add iter.count 1#usize
      ⦃z => z.val = iter.count.val + 1⦄ := by
    apply UScalar.add_spec
    have hsum : iter.count.val + (1#usize).val ≤ Std.Usize.max := by simpa using hroom
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨countNext, hadd, hcountNextRaw⟩ := WP.spec_imp_exists haddSpec
  have hcountNext : countNext.val = iter.count.val + 1 := hcountNextRaw
  let index := iter.count
  let value := iter.iter.slice[iter.iter.i]
  let iter1 : FinishIter := { iter with
    iter := { iter.iter with i := iter.iter.i + 1 }, count := countNext }
  let nextBack : FinishNextBack := fun current replacement =>
    { current with iter :=
      (match replacement with
       | none => current.iter
       | some v => { current.iter with slice := current.iter.slice.setAtNat iter.iter.i v.2 }) }
  let mutNext := { iter.iter with i := iter.iter.i + 1 }
  have hnextMut :
      core.slice.iter.IteratorIterMut.next iter.iter =
        .ok (some value, mutNext,
          fun current replacement =>
            match replacement with
            | none => current
            | some v => { current with slice := current.slice.setAtNat iter.iter.i v }) := by
    unfold core.slice.iter.IteratorIterMut.next
    rw [dif_pos hwithin]
    simp [value, mutNext]
    funext it' replacement
    cases replacement <;> rfl
  have haddNotation : (iter.count + 1#usize : Result Std.Usize) = .ok countNext := by
    change UScalar.add iter.count 1#usize = .ok countNext
    exact hadd
  have hnext :
      core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack iter =
        .ok (some (index, value), iter1, nextBack) := by
    unfold core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack
    rw [hnextMut]
    rw [haddNotation]
    simp [index, iter1, nextBack, mutNext]
    funext current replacement
    cases replacement <;> rfl
  refine ⟨index, value, iter1, nextBack, hnext, ?_, ?_, ?_, ?_⟩
  · rfl
  · exact hcountNext
  · rfl
  · rfl

private def finishStep (self : FinishBW) :
    (FinishIter × FinishBack) → Result (ControlFlow (FinishIter × FinishBack) FinishIter) :=
  fun s => BatchedWeights.finish_loop.body
    self s.1 s.2

theorem loop_success_forces_values
    (self : FinishBW) (total : Nat) (hcapacity : total ≤ Std.Usize.max)
    (iter : FinishIter) (back : FinishBack) (out : FinishIter)
    (hlen : iter.iter.slice.len.val = total)
    (hcount : iter.count.val = iter.iter.i)
    (hrun : BatchedWeights.finish_loop
      iter back self = .ok out) :
    ∀ index : Std.Usize, iter.count.val ≤ index.val → index.val < total →
      ∃ w, BatchedWeights.value self index = .ok w := by
  have hloop : Aeneas.Std.loop (finishStep self) (iter, back) = .ok out := by
    change Aeneas.Std.loop (finishStep self) (iter, back) = .ok out at hrun
    exact hrun
  induction hfuel : total - iter.count.val generalizing iter back out hlen hcount hloop with
  | zero =>
      intro index hlo hhi
      have : total ≤ iter.count.val := Nat.sub_eq_zero_iff_le.mp hfuel
      omega
  | succ fuel ih =>
      intro index hlo hhi
      have hactive : iter.iter.i < total := by
        rw [← hcount]
        have : 0 < total - iter.count.val := by rw [hfuel]; omega
        exact (Nat.sub_pos_iff_lt.mp this)
      rcases loop_success_cases (finishStep self) (iter, back) out hloop with hdone | ⟨s, hcont, htail⟩
      · have hsome := next_some_of_active iter total hactive hlen hcount hcapacity
        obtain ⟨idx, x, iter1, nextBack, hnext, _, _, _, _⟩ := hsome
        have hbody : finishStep self (iter, back) = .ok (.done out) := hdone
        unfold finishStep BatchedWeights.finish_loop.body at hbody
        rw [hnext] at hbody
        dsimp only [] at hbody
        cases hv : BatchedWeights.value self idx <;> simp [hv] at hbody
      · rcases s with ⟨iterNext, backNext⟩
        obtain ⟨indexNow, x, iter1, nextBack, hnext, hindex, hcount1, hiter1, hslice1⟩ :=
          next_some_of_active iter total hactive hlen hcount hcapacity
        have hbody : finishStep self (iter, back) =
            .ok (.cont (iterNext, backNext)) := hcont
        unfold finishStep BatchedWeights.finish_loop.body at hbody
        rw [hnext] at hbody
        dsimp only [] at hbody
        change (do
          let w ← BatchedWeights.value self indexNow
          .ok (ControlFlow.cont (iter1, fun e => back (nextBack e (some (indexNow, w)))))) =
            .ok (ControlFlow.cont (iterNext, backNext)) at hbody
        obtain ⟨w, hvalue, hcontEq⟩ := bind_success
          (BatchedWeights.value self indexNow)
          (fun w => .ok (ControlFlow.cont (iter1, fun e => back (nextBack e (some (indexNow, w))))))
          (ControlFlow.cont (iterNext, backNext)) hbody
        have hcf : ControlFlow.cont (α := FinishIter × FinishBack) (β := FinishIter)
              (iter1, fun e => back (nextBack e (some (indexNow, w)))) =
            ControlFlow.cont (α := FinishIter × FinishBack) (β := FinishIter)
              (iterNext, backNext) := by
          injection hcontEq
        have hpair :
            (iter1, fun e => back (nextBack e (some (indexNow, w)))) =
              (iterNext, backNext) := ControlFlow.cont.inj hcf
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        have hval : ∃ w, BatchedWeights.value self indexNow = .ok w := ⟨w, hvalue⟩
        by_cases hsame : index.val = iter.count.val
        · have hieq : index = indexNow := by
            apply UScalar.eq_of_val_eq
            exact hsame.trans hindex.symm
          subst index
          exact hval
        · have hltNext : iter1.count.val ≤ index.val := by omega
          have hspan : iter1.iter.i ≤ total := by rw [hiter1]; omega
          have hcountNextIter : iter1.count.val = iter1.iter.i := by rw [hcount1, hiter1, hcount]
          have hlenNext : iter1.iter.slice.len.val = total := by rw [hslice1, hlen]
          have htailLoop : Aeneas.Std.loop (finishStep self) (iter1, fun e => back (nextBack e (some (indexNow, w)))) = .ok out := by simpa using htail
          have hrunNext : BatchedWeights.finish_loop iter1
              (fun e => back (nextBack e (some (indexNow, w)))) self = .ok out := by
            change Aeneas.Std.loop (finishStep self)
              (iter1, fun e => back (nextBack e (some (indexNow, w)))) = .ok out
            exact htailLoop
          have hfuelNext : total - iter1.count.val = fuel := by
            rw [hcount1]
            have hc : iter.count.val < total := by
              have hpos : 0 < total - iter.count.val := by rw [hfuel]; omega
              exact Nat.sub_pos_iff_lt.mp hpos
            omega
          have hrest := ih iter1 (fun e => back (nextBack e (some (indexNow, w)))) out
            hlenNext hcountNextIter hrunNext htailLoop hfuelNext index hltNext hhi
          exact hrest

#print axioms loop_success_forces_values
end LoopSuccessValueLaw
end batched_weights
end AspisR1BatchedWeightsFinishExtraction
