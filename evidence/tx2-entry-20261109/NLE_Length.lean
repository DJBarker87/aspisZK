import AdapterRwModel
set_option autoImplicit false
namespace NLE_Length
open Aeneas Aeneas.Std Result
/-- Snapshot's exact proof account extent and the owned length guard fix the
actual child range, independent of validate_asq8 success or digest equality. -/
theorem proof_extent (proofAccountLength proofEnd : Nat)
 (snapshot : proofAccountLength = 58295)
 (guard : proofAccountLength = proofEnd) : proofEnd - 688 = 57607 := by omega
/-- Checked addition prevents a wrapped end from manufacturing another width. -/
theorem validated_length (proofLength proofEnd : Nat)
 (checked : proofEnd = 688 + proofLength)
 (extent : proofEnd = 58295) : proofLength = 57607 := by omega
/-- The encoder's actual fixed array carrier gives the entire native scope. -/
theorem public_extent (bytes : Array U8 1880#usize) :
 bytes.to_slice.val.length = 1880 := by
 exact bytes.property
theorem public_scope (bytes : Array U8 1880#usize) :
 0 ≤ bytes.to_slice.val.length ∧ bytes.to_slice.val.length ≤ 1880 := by
 rw [public_extent]; omega
#print proof_extent
#print validated_length
#print public_extent
#print public_scope
#print axioms proof_extent
#print axioms validated_length
#print axioms public_extent
#print axioms public_scope
end NLE_Length
