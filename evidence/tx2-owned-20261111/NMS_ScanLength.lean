import NFY_Part060
import AdapterRwCuts
set_option autoImplicit false
namespace NMS_ScanLength
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.AdapterRw.Cuts
attribute [local irreducible]
 AspisR1TerminalDecoder.pool_v1.pair_terminal.decode_pool_v1_pair_verified_afterstate_v1
 AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
/-- Every successful CLOSED scanner reply fixes57607, with no successful
codec or header fixture assumed. This is used at242's SAME scan occurrence. -/
theorem proof_length (bytes : Slice U8) (scanned : r1_pool_adapter.ScannedAsqaProof)
 (accepted : AspisR1.NFY_JHf_Scan.source bytes = .ok (.Ok scanned)) :
 scanned.proof_length = 57607#usize := by
 unfold AspisR1.NFY_JHf_Scan.source at accepted
 simp only [lift,show Usize.checked_add 688#usize 57607#usize = some 58295#usize from
  AspisR1.AdapterRw.Scalar.checked_add_eq _ _ _ (by scalar_tac),bind_tc_ok] at accepted
 repeat' first
 | (solve | cases accepted; rfl)
 | uncase_result
 | head_reduce accepted
 | split at accepted
#print axioms proof_length
end NMS_ScanLength
