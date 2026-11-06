import NKR_DigestRegularValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestRows
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
/-- Small isolated selector-address arithmetic. No field expression, array
contents or large finite enumeration is reduced by these five proofs. -/
theorem anchor_row : NKR_DigestRegularValue.row (56 : Fin 64)=(56*16+11 : Fin 1024) := by decide
theorem nullifier_row : NKR_DigestRegularValue.row (26 : Fin 64)=(26*16+11 : Fin 1024) := by decide
theorem change_row : NKR_DigestRegularValue.row (32 : Fin 64)=(32*16+11 : Fin 1024) := by decide
theorem nextRoot_row : NKR_DigestRegularValue.row (53 : Fin 64)=(53*16+11 : Fin 1024) := by decide
theorem recipient_row : NKR_DigestRegularValue.row (29 : Fin 64)=(29*16+11 : Fin 1024) := by decide
theorem g2_row (i : Fin 64) : NKR_DigestRegularValue.row i=R0P.g2Row i 11 := by rfl
#print axioms g2_row
#print axioms anchor_row
#print axioms nullifier_row
#print axioms change_row
#print axioms nextRoot_row
#print axioms recipient_row
end AspisR1.NKR_DigestRows
end
