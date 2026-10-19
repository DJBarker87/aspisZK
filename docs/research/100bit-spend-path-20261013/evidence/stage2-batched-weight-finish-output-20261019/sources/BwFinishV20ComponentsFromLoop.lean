import BwFinishV20Components
import BwFinishValueEntryBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BwFinishV20ComponentsFromLoop

abbrev FinishSlice := AspisR1BatchedWeightsFinishExtraction.batched_weights.FinishSlice
abbrev FinishQM := AspisR1BatchedWeightsExtraction.aspis_core.field.QM31
abbrev FinishBW := AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights

 theorem finish_output_value_components_of_loop_value
    (self : FinishBW) (weights : FinishSlice) (f : Nat → FinishQM)
    (hvalue : ∀ i : Std.Usize, i.val < weights.len.val →
      AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.value self i = .ok (f i.val))
    (i : Std.Usize) (hi : i.val < weights.len.val) :
    ∃ result : FinishSlice,
      AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.finish self weights = .ok result ∧
      Slice.index_usize result i = .ok (f i.val) ∧
      Nonempty (AspisR1BatchedWeightsFinishExtraction.batched_weights.HasCanonicalValueComponents
        self.raw self.terms i (f i.val)) := by
  have hentry : ∀ j : Std.Usize, j.val < weights.len.val →
      AspisR1BatchedWeightsExtraction.batched_weights.value_entry self.raw self.terms j = .ok (f j.val) := by
    intro j hj
    calc
      AspisR1BatchedWeightsExtraction.batched_weights.value_entry self.raw self.terms j =
          AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.value
            { «raw» := self.raw, terms := self.terms } j :=
        BwFinishValueEntryBridge.value_entry_eq_finish_value self.raw self.terms j
      _ = .ok (f j.val) := by
        change AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.value self j = .ok (f j.val)
        exact hvalue j hj
  exact AspisR1BatchedWeightsFinishExtraction.batched_weights.finish_output_value_components
    self weights f hvalue hentry i hi

#print axioms finish_output_value_components_of_loop_value
end BwFinishV20ComponentsFromLoop
