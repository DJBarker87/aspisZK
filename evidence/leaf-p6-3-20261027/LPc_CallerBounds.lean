import LPa_EcheckLaws
import LPa_CheckLaws
import LPa_ValidateLaws
open Aeneas Aeneas.Std Result XRk_Release
set_option autoImplicit false
namespace LPc.Echeck
theorem caller_iff (bs : Slice U8) (k : Bool) (size : bs.val.length = 928) :
    verifier.echeck bs k = ok (.Ok ()) ↔
    ∀ i, i < 29 → LPa.Echeck.predicate bs.val k i = true := by
  rw [LPa.Echeck.accepts_iff, size]
theorem tail_class (n : Nat) (bound : n < 64) :
    n < 16 ∨ (16 ≤ n ∧ n < 32) ∨ (32 ≤ n ∧ n < 48) ∨ (48 ≤ n ∧ n < 64) := by omega
/-- Count law for the actual chunks_exact semantics, with arbitrary tail. -/
theorem count_with_tail (n tail : Nat) (small : tail < 32) :
    (32*n+tail)/32 = n := by omega
#print axioms caller_iff
#print axioms tail_class
#print axioms count_with_tail
end LPc.Echeck

namespace LPc.Check
/-- Full caller bound; input bytes are arbitrary. Native/carrier join is separate. -/
theorem caller_iff (bs : Slice U8) (size : bs.val.length = 464) :
    compact.check_values bs = ok (.Ok ()) ↔
    ∀ i, i < 29 → LPa.Check.predicate bs.val i = true := by
  rw [LPa.Check.accepts_iff, size]
/-- Rejection retains the actual error, with no successful-return antecedent. -/
theorem caller_reject (bs : Slice U8) (size : bs.val.length = 464) (i : Nat)
    (bound : i < 29) (bad : LPa.Check.predicate bs.val i = false) :
    compact.check_values bs = ok (.Err .NonCanonical) := by
  exact LPa.Check.rejects_of_bad_stage bs i (by rw [size]; exact bound) bad
#print axioms caller_iff
#print axioms caller_reject
end LPc.Check

namespace LPc.Validate
theorem caller_success (row : U8) (bs : Slice U8) (size : bs.val.length = 3712)
    (valid : ∀ i, i < 116 → LPa.Validate.bad bs.val i = false) :
    r1_wire.validate_record_fields row bs = ok (.Ok ()) := by
  apply LPa.Validate.accepts_of_all_stages
  simpa only [size] using valid
theorem caller_error_bound (bs : Slice U8) (size : bs.val.length = 3712)
    (i : Nat) (hit : LPa.Validate.loop bs.val = some i) : i < 116 := by
  have h := LPa.firstBad_bound (LPa.Validate.bad bs.val) (bs.val.length/32) i hit
  simpa only [size] using h
#print axioms caller_success
#print axioms caller_error_bound
end LPc.Validate
