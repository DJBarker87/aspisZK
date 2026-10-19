import AspisR1BatchedWeightsValueActualV14
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchedWeightsValueActualV17
open AspisR1BatchedWeightsExtraction
abbrev RawVec := alloc.vec.Vec (Array Std.U64 4#usize)
theorem successful_value_has_vec
    (raw : RawVec) (terms index : Usize) (out : aspis_core.field.QM31)
    (h : batched_weights.value_entry raw terms index = .ok out) :
    ∃ lane : Array Std.U64 4#usize,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index = .ok lane := by
  cases hv : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index with
  | fail e =>
      simp [batched_weights.value_entry, batched_weights.BatchedWeights.value, hv] at h
  | ok lane => exact ⟨lane, rfl⟩
  | div => simp [batched_weights.value_entry, batched_weights.BatchedWeights.value, hv] at h
#print axioms successful_value_has_vec
end AspisR1BatchedWeightsValueActualV17
