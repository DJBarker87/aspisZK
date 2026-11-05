import NJA_FieldLaws
import RPv_RawPoseidonExternalRows

set_option autoImplicit false
noncomputable section
namespace NJA_Matrix
open Aeneas Aeneas.Std Result
open AspisR1.RawPoseidonExternalRows
abbrev K := AspisV8R15.ExactTowerBase.M31Exact

def rowArg (v : Fin 4 → U32) (r : Fin 4) : Nat := rawRowNat (fun i => (v i).val) r

theorem argument_bound (v : Fin 4 → U32) (r : Fin 4) : rowArg v r < 2^62 := by
  apply rawRowNat_lt_two_pow_62
  intro i
  exact (v i).bv.isLt

def argument (v : Fin 4 → U32) (r : Fin 4) : U64 := ⟨BitVec.ofNat 64 (rowArg v r)⟩

theorem argument_value (v : Fin 4 → U32) (r : Fin 4) : (argument v r).val = rowArg v r := by
  change rowArg v r % 2^64 = rowArg v r
  apply Nat.mod_eq_of_lt
  have := argument_bound v r
  omega

theorem cast_row (v : Fin 4 → U32) (r : Fin 4) :
    ((rowArg v r : Nat) : K) = rowFormula (fun i => ((v i).val : K)) r := by
  fin_cases r <;> simp [rowArg, rawRowNat, rowFormula]

theorem row_value (v : Fin 4 → U32) (r : Fin 4) : ∃ z : U32,
    AspisR1SelectedMaskProbe.field.M31.reduce_u62 (argument v r) = ok z ∧
    z.val < 2147483647 ∧ (z.val : K) = R0P.poseidonMat4 (fun i => ((v i).val : K)) r := by
  obtain ⟨z,hz,vz,cz⟩ := NJA_FieldLaws.reduce_u62 (argument v r)
  refine ⟨z,hz,cz,?_⟩
  rw [vz,argument_value]
  rw [← rowFormula_eq_poseidonMat4]
  rw [← cast_row]
  simp [K, AspisV8R15.ExactTowerBase.M31Exact, ZMod.natCast_mod]

#print axioms argument_bound
#print axioms argument_value
#print axioms cast_row
#print axioms row_value
end NJA_Matrix
end
