import AspisR1BatchedWeightsFinishExtraction.BatchedWeightsFinishGenerated
import BwFinishLoopSuccessValueLaw
import BwFinishValueEntryBridge
import BwFinishV20Components
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1BatchedWeightsFinishExtraction
namespace batched_weights
namespace FinishSuccessValueComponents

abbrev FinishIter := core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.IterMut aspis_core.field.QM31)
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem finish_success_exposes_loop
    (self : BatchedWeights) (weights : FinishSlice) (result : FinishSlice)
    (hfinish : BatchedWeights.finish self weights = .ok result) :
    ∃ output : FinishIter,
      BatchedWeights.finish_loop ⟨{ slice := weights }, 0#usize⟩ (fun e => e) self = .ok output ∧
      result = output.iter.slice := by
  let initial : FinishIter := ⟨{ slice := weights }, 0#usize⟩
  have h := hfinish
  unfold BatchedWeights.finish at h
  simp only [Aeneas.Std.core.slice.Slice.iter_mut, bind_tc_ok,
    core.iter.adapters.enumerate.IteratorEnumerateMut.enumerateWithBack, bind_tc_ok] at h
  change (do
    let output ← BatchedWeights.finish_loop initial (fun e => e) self
    ok output.iter.slice) = .ok result at h
  obtain ⟨output, hloop, hout⟩ := bind_success
    (BatchedWeights.finish_loop initial (fun e => e) self)
    (fun output => .ok output.iter.slice) result h
  have hslice : output.iter.slice = result := by injection hout
  exact ⟨output, hloop, hslice.symm⟩

theorem finish_success_forces_value_and_components
    (self : BatchedWeights) (weights result : FinishSlice)
    (i : Std.Usize) (hi : i.val < weights.len.val)
    (hfinish : BatchedWeights.finish self weights = .ok result) :
    ∃ w, BatchedWeights.value self i = .ok w ∧
      Nonempty (HasCanonicalValueComponents self.raw self.terms i w) := by
  obtain ⟨output, hloop, _⟩ := finish_success_exposes_loop self weights result hfinish
  let initial : FinishIter := ⟨{ slice := weights }, 0#usize⟩
  obtain ⟨w, hvalue⟩ :=
    AspisR1BatchedWeightsFinishExtraction.batched_weights.LoopSuccessValueLaw.loop_success_forces_values
      self weights.len.val weights.property initial (fun e => e) output
      (by simp [initial]) (by simp [initial]) hloop i (by simp [initial]) hi
  have hentry :
      AspisR1BatchedWeightsExtraction.batched_weights.value_entry self.raw self.terms i = .ok w := by
    calc
      AspisR1BatchedWeightsExtraction.batched_weights.value_entry self.raw self.terms i =
          BatchedWeights.value { «raw» := self.raw, terms := self.terms } i :=
        BwFinishValueEntryBridge.value_entry_eq_finish_value self.raw self.terms i
      _ = BatchedWeights.value self i := by rfl
      _ = .ok w := hvalue
  exact ⟨w, hvalue,
    AspisR1BatchedWeightsFinishExtraction.batched_weights.value_components_of_success
      self i w hentry⟩

#print axioms finish_success_exposes_loop
#print axioms finish_success_forces_value_and_components
end FinishSuccessValueComponents
end batched_weights
end AspisR1BatchedWeightsFinishExtraction
