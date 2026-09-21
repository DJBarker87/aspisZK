import AspisV8R17.GeneratedQM31Tower

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- EXPANDED GENERATED FunsChunk04.lean
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::QM31}::ONE"]
def aspis_core.field.QM31.ONE : aspis_core.field.QM31 :=
  { c0 := { a := (U32.ofNat 1), b := (U32.ofNat 0) }, c1 := { a := (U32.ofNat 0), b := (U32.ofNat 0) } }
-- END EXPANDED GENERATED

-- EXPANDED GENERATED FunsChunk06.lean
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::QM31}::ZERO"]
def aspis_core.field.QM31.ZERO : aspis_core.field.QM31 :=
  { c0 := { a := (U32.ofNat 0), b := (U32.ofNat 0) }, c1 := { a := (U32.ofNat 0), b := (U32.ofNat 0) } }
-- END EXPANDED GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedQM31Constants
open Aeneas.Std V7Tag73CurrentHelpersOpaque GeneratedQM31Scalar GeneratedQM31Tower

/-- Direct word model of pinned Rust M31(0x4000_0000), not an extracted caller. -/
def halfWord : aspis_core.field.M31 := U32.ofNat 1073741824

theorem zero_canonical : Canonical aspis_core.field.QM31.ZERO := by
  unfold aspis_core.field.QM31.ZERO
  unfold Canonical GeneratedCM31Linear.Canonical
  decide
theorem one_canonical : Canonical aspis_core.field.QM31.ONE := by
  unfold aspis_core.field.QM31.ONE
  unfold Canonical GeneratedCM31Linear.Canonical
  decide
theorem decode_zero : decode aspis_core.field.QM31.ZERO = 0 := by
  unfold aspis_core.field.QM31.ZERO
  rfl
theorem decode_one : decode aspis_core.field.QM31.ONE = 1 := by
  unfold aspis_core.field.QM31.ONE
  rfl
theorem half_value : halfWord.val = 1073741824 := rfl
theorem half_canonical : halfWord.val < RawReducer.P := by decide

theorem half_add_half : decodeScalar halfWord + decodeScalar halfWord = 1 := by
  have h : (1073741824 : QM31WordTower.M) + 1073741824 = 1 := by
    change ((1073741824 : Nat) : QM31WordTower.M) +
      ((1073741824 : Nat) : QM31WordTower.M) = 1
    rw [← Nat.cast_add]
    change ((RawReducer.P+1 : Nat) : QM31WordTower.M)=1
    rw [Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add]
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · exact h
    · rfl
  · apply QuadraticAlgebra.ext <;> rfl

theorem half_scale_correct (x : aspis_core.field.QM31) :
    ∃ z, aspis_core.field.QM31.mul_m31 x halfWord = .ok z ∧ Canonical z ∧
      decode z = decode x * decodeScalar halfWord := scalar_correct x halfWord

#print axioms zero_canonical
#print axioms one_canonical
#print axioms decode_zero
#print axioms decode_one
#print axioms half_value
#print axioms half_canonical
#print axioms half_add_half
#print axioms half_scale_correct
end AspisV8R17.GeneratedQM31Constants
