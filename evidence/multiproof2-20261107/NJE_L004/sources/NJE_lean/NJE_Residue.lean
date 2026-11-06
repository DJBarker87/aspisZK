import NJA_FieldLaws

set_option autoImplicit false
namespace NJE_Residue
open Aeneas Aeneas.Std Result

def word (n : Nat) : U32 := ⟨BitVec.ofNat 32 (n % 2147483647)⟩

theorem value (n : Nat) : (word n).val = n % 2147483647 := by
  change (n % 2147483647) % 2^32 = n % 2147483647
  apply Nat.mod_eq_of_lt
  have := Nat.mod_lt n (show 0<2147483647 by decide)
  omega

theorem canonical (n : Nat) : (word n).val < 2147483647 := by
  rw [value]
  exact Nat.mod_lt _ (by decide)

theorem multiply (x y : U32) :
    AspisR1SemanticCallExtraction.aspis_core.field.M31.mul x y =
      ok (word (x.val*y.val)) := by
  obtain ⟨z,hz,vz,cz⟩ := NJA_FieldLaws.generated_mul x y
  have eq : z=word (x.val*y.val) := UScalar.eq_of_val_eq (vz.trans (value _).symm)
  simpa [eq] using hz

#print value
#print axioms value
#print canonical
#print axioms canonical
#print multiply
#print axioms multiply
end NJE_Residue
