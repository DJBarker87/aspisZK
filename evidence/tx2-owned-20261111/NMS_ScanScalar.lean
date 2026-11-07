import NMS_ScanLength
import RSL_TX2_241
set_option autoImplicit false
namespace NMS_ScanScalar
open Aeneas Aeneas.Std AdapterRw
/-- Isolated scalar representation fact, so no scanner unfolding is used to
normalize a usize in dependent source folds. -/
theorem proof_bytes_value : (57607#usize).val = RSL.PROOF_BYTES := by
 change (57607#usize).val = 57607
 scalar_tac

theorem proof_value (bytes : Slice U8) (scanned : r1_pool_adapter.ScannedAsqaProof)
 (run : AspisR1.NFY_JHf_Scan.source bytes = .ok (.Ok scanned)) :
 scanned.proof_length.val = RSL.PROOF_BYTES := by
 rw [NMS_ScanLength.proof_length bytes scanned run]
 exact proof_bytes_value
#print axioms proof_bytes_value
#print axioms proof_value
end NMS_ScanScalar
