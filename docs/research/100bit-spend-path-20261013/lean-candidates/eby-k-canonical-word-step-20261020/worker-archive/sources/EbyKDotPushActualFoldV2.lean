import EbyKDotPushNatStep
import EbyKDotPushCanonicalFoldBridgeV1
import AspisV8R17.RawReducerNat

set_option autoImplicit false
namespace AspisR1EbyKDotPushActualFoldV2
open Aeneas Aeneas.Std Result
open AspisR1EbyKDotPushNatStep
open AspisR1.EbyKDotPushCanonicalFoldBridgeV1
open AspisR1.ExtractedCurrentReducer

abbrev U64 := UScalar UScalarTy.U64

def actualWrappingFold (x : U64) : U64 := wrappingFold x

theorem actualWrappingFold_value (x : U64) :
    (actualWrappingFold x).val = foldedRaw x.val := by
  obtain ⟨y, hy, hv⟩ := foldExecution_success x
  have hfold := fold_agrees x
  rw [hfold] at hy
  have heq : actualWrappingFold x = y := by
    exact Result.ok.inj hy
  rw [heq, hv, AspisV8R17.RawReducer.foldBits_eq_fold31]
  simp [actualWrappingFold, wrappingFold, high, foldedRaw,
    AspisV8R17.RawReducer.fold31, limbBase]

theorem actual_wrapping_fold_coordinate_step {acc raw : U64}
    (hacc : acc.val < 2 ^ 46) :
    (U64.wrapping_add acc (actualWrappingFold raw)).val =
        acc.val + foldedRaw raw.val ∧
      acc.val + foldedRaw raw.val < 2 ^ 64 ∧
      (acc.val + foldedRaw raw.val) % modulus =
        (acc.val + raw.val) % modulus := by
  have hraw : raw.val < 2 ^ 64 := raw.bv.isLt
  have heq : actualWrappingFold raw = foldedRawU64 raw hraw := by
    apply UScalar.eq_of_val_eq
    rw [actualWrappingFold_value, foldedRawU64_val]
  rw [heq]
  exact u64_coordinate_step hacc hraw

#print axioms actualWrappingFold_value
#print axioms actual_wrapping_fold_coordinate_step
end AspisR1EbyKDotPushActualFoldV2
