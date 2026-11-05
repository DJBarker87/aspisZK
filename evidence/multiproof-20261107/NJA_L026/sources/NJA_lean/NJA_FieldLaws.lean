import JFv_RawExtractedSemanticCallOpsV20
import ExtractedMaskReducer
import RawPoseidonExtensionWords

set_option autoImplicit false
noncomputable section
namespace NJA_FieldLaws
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem generated_mul (x y : U32) : ∃ z : U32,
    AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x y = ok z ∧
    z.val = (x.val*y.val) % 2147483647 ∧ z.val < 2147483647 := by
  rw [generated_m31_mul_eq_probe]
  exact AspisR1.ExtractedMaskReducer.current_mul_mod x y

-- Safe reference transcription of the frozen three-call pow5 expression.
-- This is not identified with an adopted Poseidon cohort by this definition.
def pow5_ref (x : U32) : Result U32 := do
  let square ← AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x x
  let fourth ← AspisR1SemanticCallExtraction.aspis_core.field.M31.mul square square
  AspisR1SemanticCallExtraction.aspis_core.field.M31.mul fourth x

theorem pow5_value (x : U32) : ∃ z : U32,
    pow5_ref x = ok z ∧ z.val = x.val^5 % 2147483647 ∧ z.val < 2147483647 := by
  obtain ⟨square,hs,vs,cs⟩ := generated_mul x x
  obtain ⟨fourth,hf,vf,cf⟩ := generated_mul square square
  obtain ⟨z,hz,vz,cz⟩ := generated_mul fourth x
  refine ⟨z, ?_, ?_, cz⟩
  · simp only [pow5_ref,hs,hf,hz,bind_tc_ok]
  · rw [vz,vf,vs]
    simp only [pow_succ, pow_zero, Nat.one_mul, Nat.mul_one]
    simp only [← Nat.mul_mod, Nat.mod_mod, Nat.mul_assoc]

theorem reduce_u62 (x : U64) : ∃ z : U32,
    AspisR1SelectedMaskProbe.field.M31.reduce_u62 x = ok z ∧
    z.val = x.val % 2147483647 ∧ z.val < 2147483647 := by
  exact AspisR1.RawPoseidonExtensionWords.current_reduce_u62_mod x

#print axioms generated_mul
#print axioms pow5_value
#print axioms reduce_u62
end NJA_FieldLaws
end
