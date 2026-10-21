import S8Kani2MutableSource
import AspisR1BatchedWeightsValueActualV19

set_option autoImplicit false
noncomputable section
namespace S8Kani2MutableValue
open Aeneas Aeneas.Std Result
namespace F
abbrev BW := AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights
abbrev Q := AspisR1BatchedWeightsFinishExtraction.aspis_core.field.QM31
abbrev value := AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.value
end F

/-- Reducer identity to the retained concrete arithmetic extraction. -/
theorem reducer_eq (x : U64) :
    AspisR1BatchedWeightsFinishExtraction.aspis_core.field.M31.reduce_u64 x =
      AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x := by
  unfold AspisR1BatchedWeightsFinishExtraction.aspis_core.field.M31.reduce_u64
    AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64
    AspisR1BatchedWeightsFinishExtraction.aspis_core.field.reduce_u64
    AspisR1BatchedWeightsExtraction.aspis_core.field.reduce_u64
    AspisR1BatchedWeightsFinishExtraction.aspis_core.field.P
    AspisR1BatchedWeightsExtraction.aspis_core.field.P
  rfl

theorem value_eq_entry (self : F.BW) (index : Usize) :
    F.value self index = AspisR1BatchedWeightsExtraction.batched_weights.value_entry
      self.raw self.terms index := by
  unfold F.value AspisR1BatchedWeightsFinishExtraction.batched_weights.BatchedWeights.value
    AspisR1BatchedWeightsExtraction.batched_weights.value_entry
    AspisR1BatchedWeightsExtraction.batched_weights.BatchedWeights.value
  simp only [reducer_eq]

/-- Total local value, with no canonicality assumption on raw U64 lanes. -/
theorem value_total (self : F.BW) (index : Usize)
    (hi : index.val < self.raw.length) :
    ∃ out : F.Q, F.value self index = .ok out := by
  obtain ⟨row,hread,_⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec self.raw index hi)
  have hread' : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) self.raw index=.ok row := by
    rw [alloc.vec.Vec.index_slice_index]; exact hread
  obtain ⟨x0,x1,x2,x3,m0,m1,m2,m3,_,_,_,_,_,_,_,_,hout,_⟩ :=
    AspisR1BatchedWeightsValueActualV19.value_entry_of_vec_success_canonical
      self.raw self.terms index row hread'
  exact ⟨_,by rw [value_eq_entry]; exact hout⟩

def valueAt (self : F.BW) (j : Nat) : F.Q :=
  if hj : j < self.raw.length then
    (value_total self (UScalar.ofNatCore j (by have hp := self.raw.property; omega))
      (by exact hj)).choose
  else ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem valueAt_success (self : F.BW) (index : Usize)
    (hi : index.val < self.raw.length) :
    F.value self index=.ok (valueAt self index.val) := by
  unfold valueAt
  rw [dif_pos hi]
  have heq : UScalar.ofNatCore index.val (by have hp := self.raw.property; omega) = index := by
    apply UScalar.ext
    rfl
  simp only [heq]
  exact (value_total self index hi).choose_spec

#print axioms reducer_eq
#print axioms value_eq_entry
#print axioms value_total
#print axioms valueAt_success
end S8Kani2MutableValue
