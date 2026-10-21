import S8Kani2MutableLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1BatchedWeightsFinishExtraction
namespace batched_weights
theorem finish_output_invariant
    (self : BatchedWeights) (weights : FinishSlice)
    (f : Nat → aspis_core.field.QM31)
    (hvalue : ∀ i : Std.Usize, i.val < weights.len.val →
      BatchedWeights.value self i = .ok (f i.val)) :
    ∃ result : FinishSlice,
      BatchedWeights.finish self weights = .ok result ∧
      result = prefixWrite f 0 weights.len.val weights := by
  let initial : FinishIter := ⟨{ slice := weights }, 0#usize⟩
  have hstart : initial.iter.i ≤ (initial.iter.slice.len).val := by
    simp [initial]
  have hcount : initial.count.val = initial.iter.i := by
    simp [initial]
  have hcapacity : weights.len.val ≤ Std.Usize.max := by
    exact weights.property
  obtain ⟨output, hrun, hslice⟩ :=
    finish_loop_output_invariant_of_values self initial f hstart hcount
      (by simpa [initial] using hvalue) hcapacity
  refine ⟨output.iter.slice, ?_, hslice⟩
  unfold BatchedWeights.finish
  simp only [Aeneas.Std.core.slice.Slice.iter_mut, bind_tc_ok,
    core.iter.adapters.enumerate.IteratorEnumerateMut.enumerateWithBack, bind_tc_ok]
  change (do
    let back ← BatchedWeights.finish_loop initial (fun e => e) self
    ok back.iter.slice) = .ok output.iter.slice
  rw [hrun]
  rfl

#print axioms finish_output_invariant
end batched_weights
end AspisR1BatchedWeightsFinishExtraction
