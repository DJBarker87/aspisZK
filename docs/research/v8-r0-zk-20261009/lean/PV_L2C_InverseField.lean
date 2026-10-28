import PV_L2C_NativeInverse
import R0Z.M31Prime
set_option autoImplicit false
namespace PV_L2C_InverseField
open Aeneas Aeneas.Std Result PV_L2C_M31
local instance : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩

theorem decoded (x : word) (hz : decode x ≠ 0) :
    decode (PV_L2C_NativeInverse.chain x) = (decode x)⁻¹ := by
  rw [PV_L2C_NativeInverse.decoded_chain]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  exact ZMod.pow_card_sub_one_eq_one hz
#print axioms decoded

theorem complete (x : word) (hx : canonical x) (hz : decode x ≠ 0) :
    PV_L2C_NativeInverse.run x = ok (PV_L2C_NativeInverse.chain x) ∧
    canonical (PV_L2C_NativeInverse.chain x) ∧
    decode (PV_L2C_NativeInverse.chain x) = (decode x)⁻¹ :=
  ⟨(PV_L2C_NativeInverse.success x hx hz).1,PV_L2C_NativeInverse.canonical_chain x,decoded x hz⟩
#print axioms complete
end PV_L2C_InverseField
