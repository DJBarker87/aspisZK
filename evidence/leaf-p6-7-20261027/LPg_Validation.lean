import LPg_StopRule
import LPc_CallerBounds
open Aeneas Aeneas.Std Result XRk_Release
set_option autoImplicit false
namespace LPg
/-- A reached bad stage keeps its exact original error through the remaining 116 stages. -/
theorem validation_error (row : U8) (bs : Slice U8) (size : bs.val.length = 3712)
    (n i : Nat) (bound : n ≤ 116)
    (hit : LPa.firstBad (LPa.Validate.bad bs.val) n = some i) :
    ∃ h : i ≤ UScalar.cMax .Usize,
      r1_wire.validate_record_fields row bs = ok (.Err (.NonCanonical row (UScalar.ofNat i h))) := by
  have final : LPa.Validate.loop bs.val = some i := by
    unfold LPa.Validate.loop
    rw [size]
    exact first_error_sticky _ n 116 i bound hit
  exact ⟨LPa.Validate.error_index_bound bs (by omega) i final,
    LPa.Validate.error_exact row bs (by omega) i final⟩
#print axioms validation_error
end LPg
