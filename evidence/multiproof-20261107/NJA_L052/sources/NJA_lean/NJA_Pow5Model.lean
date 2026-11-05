import NJA_FieldLaws
import R0P.Poseidon

set_option autoImplicit false
noncomputable section
namespace NJA_Pow5Model
open Aeneas Aeneas.Std Result
abbrev K := AspisV8R15.ExactTowerBase.M31Exact

theorem reference (x : U32) : ∃ z : U32,
    NJA_FieldLaws.pow5_ref x = ok z ∧ z.val < 2147483647 ∧
    (z.val : K) = R0P.poseidonPow5 (x.val : K) := by
  obtain ⟨z,hz,vz,cz⟩ := NJA_FieldLaws.pow5_value x
  refine ⟨z,hz,cz,?_⟩
  rw [vz,R0P.poseidon_pow5_eq]
  simp [K, AspisV8R15.ExactTowerBase.M31Exact, ZMod.natCast_mod]

#print axioms reference
end NJA_Pow5Model
end
