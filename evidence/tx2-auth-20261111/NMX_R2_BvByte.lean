import NMX_R2_ScalarCarrier
set_option autoImplicit false
namespace NMX_R2_BvByte
open Aeneas Aeneas.Std NMX_R2_Carrier
/-- Isolated scalar wrapper, without a Scalar.val simp rewrite loop. -/
theorem value (v : BitVec 8) : (byte (⟨v⟩ : U8)).toNat = v.toNat :=
 NMX_R2_ScalarCarrier.byte_value (⟨v⟩ : U8)

theorem low {n : Nat} (v : BitVec n) :
 (byte (⟨v.setWidth 8⟩ : U8)).toNat = v.toNat % 256 := by
 rw [value,BitVec.toNat_setWidth]
#print axioms value
#print axioms low
end NMX_R2_BvByte
