import AspisR1BatchedWeightsExtraction.Funs
import ExtractedCurrentReducer

/-! The emitted rho value accessor is total at every in-bounds row, even for
unrestricted stored U64 lanes. All four outputs are canonical. -/
set_option autoImplicit false
namespace AspisR1.R22BatchedValueTotal
open Aeneas Aeneas.Std Result
open AspisR1BatchedWeightsExtraction
abbrev BW := batched_weights.BatchedWeights
abbrev Q := aspis_core.field.QM31

/-- Definitional transport between the two retained reducer emissions. -/
theorem reducer_eq (x : U64) :
    aspis_core.field.M31.reduce_u64 x = AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x := by
  unfold aspis_core.field.M31.reduce_u64 aspis_core.field.reduce_u64
    AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64
    AspisR1Qm31ArithmeticProbe.field.reduce_u64
    aspis_core.field.P AspisR1Qm31ArithmeticProbe.field.P
  rfl

theorem value_total (self : BW) (index : Usize) (hi : index.val < self.raw.length) :
    ∃ out : Q, batched_weights.BatchedWeights.value self index = .ok out ∧
      out.c0.a.val < 2147483647 ∧ out.c0.b.val < 2147483647 ∧
      out.c1.a.val < 2147483647 ∧ out.c1.b.val < 2147483647 := by
  obtain ⟨lane, hlane, _⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec self.raw index hi)
  have hvec : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      (Array U64 4#usize)) self.raw index = .ok lane := by
    rw [alloc.vec.Vec.index_slice_index]
    exact hlane
  obtain ⟨x0, h0, _⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 0#usize (by simp [lane.property]))
  obtain ⟨x1, h1, _⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 1#usize (by simp [lane.property]))
  obtain ⟨x2, h2, _⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 2#usize (by simp [lane.property]))
  obtain ⟨x3, h3, _⟩ := WP.spec_imp_exists (Array.index_usize_spec lane 3#usize (by simp [lane.property]))
  obtain ⟨z0, hz0, _, hc0⟩ := ExtractedCurrentReducer.current_wrapper_mod x0
  obtain ⟨z1, hz1, _, hc1⟩ := ExtractedCurrentReducer.current_wrapper_mod x1
  obtain ⟨z2, hz2, _, hc2⟩ := ExtractedCurrentReducer.current_wrapper_mod x2
  obtain ⟨z3, hz3, _, hc3⟩ := ExtractedCurrentReducer.current_wrapper_mod x3
  refine ⟨⟨⟨z0,z1⟩,⟨z2,z3⟩⟩, ?_, hc0, hc1, hc2, hc3⟩
  simp only [batched_weights.BatchedWeights.value, hvec, bind_tc_ok, h0, h1, h2, h3,
    reducer_eq, hz0, hz1, hz2, hz3]
  rfl

#print axioms reducer_eq
#print axioms value_total
end AspisR1.R22BatchedValueTotal
