import AspisR1BatchedWeightsValueActualV17
import AspisR1BatchedWeightsValueActualV19
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchedWeightsValueActualV20
open AspisR1BatchedWeightsExtraction
abbrev RawVec := alloc.vec.Vec (Array Std.U64 4#usize)
abbrev M := aspis_core.field.M31
abbrev Q := aspis_core.field.QM31
theorem successful_value_canonical_components
    (raw : RawVec) (terms index : Usize) (out : Q)
    (h : batched_weights.value_entry raw terms index = .ok out) :
    ∃ (lane : Array Std.U64 4#usize) (x0 x1 x2 x3 : Std.U64) (m0 m1 m2 m3 : M),
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize)) raw index = .ok lane ∧
      Array.index_usize lane 0#usize = .ok x0 ∧
      Array.index_usize lane 1#usize = .ok x1 ∧
      Array.index_usize lane 2#usize = .ok x2 ∧
      Array.index_usize lane 3#usize = .ok x3 ∧
      aspis_core.field.M31.reduce_u64 x0 = .ok m0 ∧
      aspis_core.field.M31.reduce_u64 x1 = .ok m1 ∧
      aspis_core.field.M31.reduce_u64 x2 = .ok m2 ∧
      aspis_core.field.M31.reduce_u64 x3 = .ok m3 ∧
      out = AspisR1BatchedWeightsValueActualV19.qOf m0 m1 m2 m3 ∧
      m0.val = x0.val % AspisV8R17.RawReducer.P ∧ m0.val < AspisV8R17.RawReducer.P ∧
      m1.val = x1.val % AspisV8R17.RawReducer.P ∧ m1.val < AspisV8R17.RawReducer.P ∧
      m2.val = x2.val % AspisV8R17.RawReducer.P ∧ m2.val < AspisV8R17.RawReducer.P ∧
      m3.val = x3.val % AspisV8R17.RawReducer.P ∧ m3.val < AspisV8R17.RawReducer.P := by
  obtain ⟨lane, hvec⟩ := AspisR1BatchedWeightsValueActualV17.successful_value_has_vec raw terms index out h
  obtain ⟨x0, x1, x2, x3, m0, m1, m2, m3, h0, h1, h2, h3,
    r0, r1, r2, r3, hcalc, hm0, hc0, hm1, hc1, hm2, hc2, hm3, hc3⟩ :=
    AspisR1BatchedWeightsValueActualV19.value_entry_of_vec_success_canonical raw terms index lane hvec
  have hout : out = AspisR1BatchedWeightsValueActualV19.qOf m0 m1 m2 m3 :=
    Result.ok.inj (h.symm.trans hcalc)
  exact ⟨lane, x0, x1, x2, x3, m0, m1, m2, m3,
    hvec, h0, h1, h2, h3, r0, r1, r2, r3, hout, hm0, hc0, hm1, hc1, hm2, hc2, hm3, hc3⟩
#print axioms successful_value_canonical_components
end AspisR1BatchedWeightsValueActualV20
