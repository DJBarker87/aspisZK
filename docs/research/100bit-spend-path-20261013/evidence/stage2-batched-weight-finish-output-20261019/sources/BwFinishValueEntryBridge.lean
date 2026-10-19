import AspisR1BatchedWeightsExtraction.Funs
import AspisR1BatchedWeightsFinishExtraction.BatchedWeightsFinishGenerated
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace BwFinishValueEntryBridge

theorem field_P_eq : AspisR1BatchedWeightsFinishExtraction.aspis_core.field.P = AspisR1BatchedWeightsExtraction.aspis_core.field.P := by
  unfold AspisR1BatchedWeightsFinishExtraction.aspis_core.field.P
    AspisR1BatchedWeightsExtraction.aspis_core.field.P
  rfl

theorem field_reduce_u64_eq (x : Std.U64) :
    AspisR1BatchedWeightsFinishExtraction.aspis_core.field.reduce_u64 x = AspisR1BatchedWeightsExtraction.aspis_core.field.reduce_u64 x := by
  unfold AspisR1BatchedWeightsFinishExtraction.aspis_core.field.reduce_u64 AspisR1BatchedWeightsExtraction.aspis_core.field.reduce_u64
  simp only [field_P_eq]

theorem m31_reduce_u64_eq (x : Std.U64) :
    AspisR1BatchedWeightsFinishExtraction.aspis_core.field.M31.reduce_u64 x = AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x := by
  unfold AspisR1BatchedWeightsFinishExtraction.aspis_core.field.M31.reduce_u64 AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64
  rw [field_reduce_u64_eq]

theorem batched_value_eq (self : AspisR1BatchedWeightsExtraction.batched_weights.BatchedWeights) (i : Std.Usize) :
    AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.value self i =
      AspisR1BatchedWeightsExtraction.batched_weights.BatchedWeights.value self i := by
  unfold AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.value AspisR1BatchedWeightsExtraction.batched_weights.BatchedWeights.value
  simp only [m31_reduce_u64_eq]

theorem value_entry_eq_finish_value (raw : alloc.vec.Vec (Array Std.U64 4#usize))
    (terms i : Std.Usize) :
    AspisR1BatchedWeightsExtraction.batched_weights.value_entry raw terms i =
      AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.value { «raw» := raw, terms } i := by
  unfold AspisR1BatchedWeightsExtraction.batched_weights.value_entry
  rw [← batched_value_eq]

#print axioms field_P_eq
#print axioms field_reduce_u64_eq
#print axioms m31_reduce_u64_eq
#print axioms batched_value_eq
#print axioms value_entry_eq_finish_value
end BwFinishValueEntryBridge
