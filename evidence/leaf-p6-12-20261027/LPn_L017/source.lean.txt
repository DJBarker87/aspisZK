import LPl_A_EcheckLaws
import LPl_A_CheckLaws
import LPl_A_ValidateLaws
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPl_C.Echeck
theorem caller_iff (bs : Slice U8) (k : Bool) (size : bs.val.length = 928) :
    verifier.echeck bs k = ok (.Ok ()) ↔
    ∀ i, i < 29 → LPl_A.Echeck.predicate bs.val k i = true := by
  rw [LPl_A.Echeck.accepts_iff, size]
theorem tail_class (n : Nat) (bound : n < 64) :
    n < 16 ∨ (16 ≤ n ∧ n < 32) ∨ (32 ≤ n ∧ n < 48) ∨ (48 ≤ n ∧ n < 64) := by omega
/-- Count law for the actual chunks_exact semantics, with arbitrary tail. -/
theorem count_with_tail (n tail : Nat) (small : tail < 32) :
    (32*n+tail)/32 = n := by omega
#print axioms caller_iff
#print axioms tail_class
#print axioms count_with_tail
end LPl_C.Echeck

namespace LPl_C.Check
/-- Full caller bound; input bytes are arbitrary. Native/carrier join is separate. -/
theorem caller_iff (bs : Slice U8) (size : bs.val.length = 464) :
    compact.check_values bs = ok (.Ok ()) ↔
    ∀ i, i < 29 → LPl_A.Check.predicate bs.val i = true := by
  rw [LPl_A.Check.accepts_iff, size]
/-- Rejection retains the actual error, with no successful-return antecedent. -/
theorem caller_reject (bs : Slice U8) (size : bs.val.length = 464) (i : Nat)
    (bound : i < 29) (bad : LPl_A.Check.predicate bs.val i = false) :
    compact.check_values bs = ok (.Err .NonCanonical) := by
  exact LPl_A.Check.rejects_of_bad_stage bs i (by rw [size]; exact bound) bad
#print axioms caller_iff
#print axioms caller_reject
end LPl_C.Check

namespace LPl_C.Validate
theorem caller_success (row : U8) (bs : Slice U8) (size : bs.val.length = 3712)
    (valid : ∀ i, i < 116 → LPl_A.Validate.bad bs.val i = false) :
    r1_wire.validate_record_fields row bs = ok (.Ok ()) := by
  apply LPl_A.Validate.accepts_of_all_stages
  simpa only [size] using valid
theorem caller_error_bound (bs : Slice U8) (size : bs.val.length = 3712)
    (i : Nat) (hit : LPl_A.Validate.loop bs.val = some i) : i < 116 := by
  have h := LPl_A.firstBad_bound (LPl_A.Validate.bad bs.val) (bs.val.length/32) i hit
  simpa only [size] using h
#print axioms caller_success
#print axioms caller_error_bound
end LPl_C.Validate
