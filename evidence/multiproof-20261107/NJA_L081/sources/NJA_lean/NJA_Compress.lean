import NJA_Matrix
import ExtractedMaskM31AddSub
import R0P.Semantics

set_option autoImplicit false
noncomputable section
namespace NJA_Compress
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev K := NJA_Matrix.K

theorem add_law (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
 ∃ z : U32, AspisR1SemanticCallExtraction.aspis_core.field.M31.add x y = ok z ∧
 z.val<2147483647 ∧ (z.val:K)=(x.val:K)+(y.val:K) := by
 rw [generated_m31_add_eq_probe]
 obtain ⟨z,hz,vz,cz⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x y hx hy
 refine ⟨z,hz,cz,?_⟩
 rw [vz]
 simp [K,NJA_Matrix.K,AspisV8R15.ExactTowerBase.M31Exact,ZMod.natCast_mod,
   AspisR1.ExtractedMaskM31AddSub.P]

theorem tweak : (1095962629:K) = -(1051521018:K) := by
 norm_num [K,NJA_Matrix.K,AspisV8R15.ExactTowerBase.M31Exact]

def seed (left right : Fin 8 → K) (i : Fin 16) : K :=
 if h : i.val<8 then left ⟨i.val,h⟩ else
 if i.val=15 then right 7+1095962629 else right ⟨i.val-8,by omega⟩

theorem seed_model (left right : Fin 8 → K) :
 seed left right = fun i : Fin 16 =>
   if h : i.val<8 then left ⟨i.val,h⟩ else
   if i.val=15 then right 7-1051521018 else right ⟨i.val-8,by omega⟩ := by
 funext i
 simp only [seed,tweak,sub_eq_add_neg]

-- Exact caller argument formation, before the still-open permutation bridge.
theorem lane15 (right : Fin 8 → U32) (h : (right 7).val<2147483647) : ∃ z : U32,
 AspisR1SemanticCallExtraction.aspis_core.field.M31.add (right 7) 1095962629#u32 = ok z ∧
 z.val<2147483647 ∧ (z.val:K)=((right 7).val:K)-1051521018 := by
 obtain ⟨z,hz,cz,vz⟩ := add_law (right 7) 1095962629#u32 h (by decide)
 refine ⟨z,hz,cz,?_⟩
 simpa only [show (1095962629#u32).val=1095962629 from rfl,tweak,sub_eq_add_neg] using vz

#print axioms add_law
#print axioms tweak
#print axioms seed_model
#print axioms lane15
end NJA_Compress
end
