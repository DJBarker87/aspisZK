import AspisR1BatchedWeightsFinishExtraction.BatchedWeightsFinishGenerated
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace BwFinishBodySuccessInversion
abbrev FinishIter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut AspisR1BatchedWeightsFinishExtraction.aspis_core.field.QM31)
abbrev FinishBack := FinishIter → FinishIter
abbrev FinishNextBack := FinishIter → Option (Std.Usize × AspisR1BatchedWeightsFinishExtraction.aspis_core.field.QM31) → FinishIter

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem cont_success_forces_value_success
    (self : AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights)
    (iter : FinishIter) (back : FinishBack)
    (index : Std.Usize) (x : AspisR1BatchedWeightsFinishExtraction.aspis_core.field.QM31)
    (iter1 : FinishIter) (nextBack : FinishNextBack)
    (hout : FinishIter × FinishBack)
    (hnext : AspisR1BatchedWeightsFinishExtraction.core.iter.adapters.enumerate.IteratorEnumerateMut.nextWithBack iter =
      .ok (some (index, x), iter1, nextBack))
    (hbody : AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.finish_loop.body self iter back =
      .ok (ControlFlow.cont hout)) :
    ∃ w, AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.value self index = .ok w := by
  unfold AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.finish_loop.body at hbody
  rw [hnext] at hbody
  simp only [bind_tc_ok] at hbody
  obtain ⟨w, hvalue, _⟩ := bind_success
    (AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.value self index)
    (fun w => .ok (ControlFlow.cont (iter1, fun e => back (nextBack e (some (index, w))))))
    (ControlFlow.cont hout) hbody
  exact ⟨w, hvalue⟩

#print axioms cont_success_forces_value_success
end BwFinishBodySuccessInversion
