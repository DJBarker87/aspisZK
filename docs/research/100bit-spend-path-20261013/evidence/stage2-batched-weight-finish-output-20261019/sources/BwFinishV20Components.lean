import AspisR1BatchedWeightsValueActualV20
import AspisR1BatchedWeightsFinishExtraction.BatchedWeightsFinishSliceOutputInvariant
import BwPrefixWriteIndex
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchedWeightsFinishExtraction
namespace batched_weights

abbrev FinishQM := AspisR1BatchedWeightsExtraction.aspis_core.field.QM31

structure HasCanonicalValueComponents (raw : alloc.vec.Vec (Array Std.U64 4#usize))
    (terms index : Std.Usize) (out : FinishQM) where
  lane : Array Std.U64 4#usize
  x0 : Std.U64
  x1 : Std.U64
  x2 : Std.U64
  x3 : Std.U64
  m0 : AspisR1BatchedWeightsValueActualV20.M
  m1 : AspisR1BatchedWeightsValueActualV20.M
  m2 : AspisR1BatchedWeightsValueActualV20.M
  m3 : AspisR1BatchedWeightsValueActualV20.M
  hvec : alloc.vec.Vec.index
    (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index = .ok lane
  h0 : Array.index_usize lane 0#usize = .ok x0
  h1 : Array.index_usize lane 1#usize = .ok x1
  h2 : Array.index_usize lane 2#usize = .ok x2
  h3 : Array.index_usize lane 3#usize = .ok x3
  r0 : AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x0 = .ok m0
  r1 : AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x1 = .ok m1
  r2 : AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x2 = .ok m2
  r3 : AspisR1BatchedWeightsExtraction.aspis_core.field.M31.reduce_u64 x3 = .ok m3
  hout : out = AspisR1BatchedWeightsValueActualV19.qOf m0 m1 m2 m3

theorem value_components_of_success
    (self : BatchedWeights) (i : Std.Usize) (out : FinishQM)
    (hentry : AspisR1BatchedWeightsExtraction.batched_weights.value_entry
      self.raw self.terms i = .ok out) :
    Nonempty (HasCanonicalValueComponents self.raw self.terms i out) := by
  obtain ⟨lane, x0, x1, x2, x3, m0, m1, m2, m3,
    hvec, h0, h1, h2, h3, r0, r1, r2, r3, hout, hm0, hc0, hm1, hc1, hm2, hc2, hm3, hc3⟩ :=
    @AspisR1BatchedWeightsValueActualV20.successful_value_canonical_components
      self.raw self.terms i out hentry
  exact ⟨⟨lane, x0, x1, x2, x3, m0, m1, m2, m3, hvec, h0, h1, h2, h3, r0, r1, r2, r3, hout⟩⟩

theorem finish_output_value_components
    (self : BatchedWeights) (weights : FinishSlice)
    (f : Nat → FinishQM)
    (hvalue : ∀ i : Std.Usize, i.val < weights.len.val →
      BatchedWeights.value self i = .ok (f i.val))
    (hentry : ∀ i : Std.Usize, i.val < weights.len.val →
      AspisR1BatchedWeightsExtraction.batched_weights.value_entry
        self.raw self.terms i = .ok (f i.val))
    (i : Std.Usize) (hi : i.val < weights.len.val) :
    ∃ result : FinishSlice,
      BatchedWeights.finish self weights = .ok result ∧
      Slice.index_usize result i = .ok (f i.val) ∧
      Nonempty (HasCanonicalValueComponents self.raw self.terms i (f i.val)) := by
  obtain ⟨result, hfinish, hprefix⟩ := finish_output_invariant self weights f hvalue
  have hread : Slice.index_usize result i = .ok (f i.val) := by
    rw [hprefix]
    exact BwPrefixWriteIndex.prefixWrite_index f weights.len.val weights i le_rfl hi
  have hcomponents : Nonempty (HasCanonicalValueComponents self.raw self.terms i (f i.val)) :=
    value_components_of_success self i (f i.val) (hentry i hi)
  exact ⟨result, hfinish, hread, hcomponents⟩

#print axioms value_components_of_success
#print axioms finish_output_value_components
end batched_weights
end AspisR1BatchedWeightsFinishExtraction
