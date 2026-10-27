import LPl_Validate
import LPl_Coimport
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPl.Validate

theorem native_success (row : U8) (bs : Slice U8)
    (trace : LPl.Scan.Trace (predicate bs.val) (bs.val.length/32) 0 none) :
    r1_wire.validate_record_fields row bs = ok (.Ok ()) := by
  rw [LPl_A.Validate.shipped_leaf_model,← first_error bs.val none trace]

theorem native_error (row : U8) (bs : Slice U8) (i : Nat)
    (size : bs.val.length ≤ 3712)
    (trace : LPl.Scan.Trace (predicate bs.val) (bs.val.length/32) 0 (some i)) :
    r1_wire.validate_record_fields row bs =
      ok (.Err (.NonCanonical row (UScalar.ofNat i (error_bound bs i size trace).2))) := by
  exact LPl_A.Validate.error_exact row bs size i (first_error bs.val (some i) trace).symm

#print axioms bad_eq
#print axioms window
#print axioms first_error
#print axioms native_result
#print axioms error_bound
#print axioms earlier_error
#print axioms unique
#print axioms total
#print axioms native_success
#print axioms native_error
#print axioms LPl_G.first_error_sticky
#print axioms LPl_G.validation_error
end LPl.Validate
