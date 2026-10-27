import R1Z.PV_Src_PortField
import R1Z.PV_Src_CanonicalFieldEquality
import R0Z.PoseidonCanon

set_option autoImplicit false
namespace R1Z.PV_Src_PortAddCopy
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort

theorem source (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    aspis_core.field.M31.add a b = R0PoseidonCopy.m31_add a b := by
  letI : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
  obtain ⟨x,hx,hcx,hfx⟩ := PV_Src_PortField.addition (K := ZMod 2147483647) a b ha hb
  obtain ⟨y,hy,hfy⟩ := add_lift (K := ZMod 2147483647) a b
  obtain ⟨z,hz,hcz⟩ := add_canon a b
  have hyz : y=z := Result.ok.inj (hy.symm.trans hz)
  have hcy : y.val < 2147483647 := by rw [hyz];exact hcz
  have hxy := PV_Src_CanonicalFieldEquality.word x y hcx hcy (hfx.trans hfy.symm)
  rw [hx,hy,hxy]

#print axioms source
end R1Z.PV_Src_PortAddCopy
