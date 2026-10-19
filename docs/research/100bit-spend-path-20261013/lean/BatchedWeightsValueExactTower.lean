import AspisR1BatchedWeightsValueActualV20
import ExtractedMaskQM31Exact

set_option autoImplicit false
namespace AspisR1.BatchedWeightsValueExactTower
open Aeneas Aeneas.Std Result
open AspisR1BatchedWeightsExtraction

abbrev RawVec := alloc.vec.Vec (Array Std.U64 4#usize)
abbrev Q := aspis_core.field.QM31
abbrev ExactQ := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev ExactM := AspisR1.ExtractedMaskQM31Exact.M31Exact

def toProbe (x : Q) : AspisR1.ExtractedMaskQM31Exact.CurrentQM :=
  ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩

def rawDecode (x0 x1 x2 x3 : Std.U64) : ExactQ :=
  ⟨⟨(x0.val : ExactM), (x1.val : ExactM)⟩,
    ⟨(x2.val : ExactM), (x3.val : ExactM)⟩⟩

theorem cast_modulus (n : Nat) :
    ((n % AspisV8R17.RawReducer.P : Nat) : ExactM) = (n : ExactM) := by
  exact ZMod.natCast_mod n AspisV8R17.RawReducer.P

/-- A successful actual generated value call yields canonical exact-field
coordinates equal to its four actual raw U64 reads, with no raw-value bound
or assumed reducer-success premise. -/
theorem successful_value_exact
    (raw : RawVec) (terms index : Usize) (out : Q)
    (h : batched_weights.value_entry raw terms index = .ok out) :
    ∃ (lane : Array Std.U64 4#usize) (x0 x1 x2 x3 : Std.U64),
      alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize))
        raw index = .ok lane ∧
      Array.index_usize lane 0#usize = .ok x0 ∧
      Array.index_usize lane 1#usize = .ok x1 ∧
      Array.index_usize lane 2#usize = .ok x2 ∧
      Array.index_usize lane 3#usize = .ok x3 ∧
      AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM (toProbe out) ∧
      AspisR1.ExtractedMaskQM31Exact.decode (toProbe out) = rawDecode x0 x1 x2 x3 := by
  obtain ⟨lane, x0, x1, x2, x3, m0, m1, m2, m3,
    hvec, h0, h1, h2, h3, _r0, _r1, _r2, _r3,
    hout, hm0, hc0, hm1, hc1, hm2, hc2, hm3, hc3⟩ :=
    AspisR1BatchedWeightsValueActualV20.successful_value_canonical_components
      raw terms index out h
  refine ⟨lane, x0, x1, x2, x3, hvec, h0, h1, h2, h3, ?_, ?_⟩
  · rw [hout]
    exact ⟨⟨hc0, hc1⟩, ⟨hc2, hc3⟩⟩
  · rw [hout]
    change (⟨⟨(m0.val : ExactM), (m1.val : ExactM)⟩,
      ⟨(m2.val : ExactM), (m3.val : ExactM)⟩⟩ : ExactQ) = rawDecode x0 x1 x2 x3
    rw [hm0, hm1, hm2, hm3, cast_modulus, cast_modulus, cast_modulus, cast_modulus]
    rfl

#print axioms cast_modulus
#print axioms successful_value_exact
end AspisR1.BatchedWeightsValueExactTower
