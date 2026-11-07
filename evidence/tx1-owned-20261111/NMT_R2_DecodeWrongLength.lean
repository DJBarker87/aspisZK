import NMT_345Decoder
import NMT_R2_Scalar
import NMT_R2_DecodeConstants
set_option autoImplicit false
noncomputable section
namespace NMT_R2_DecodeWrongLength
open Aeneas Aeneas.Std NMT_345

theorem wrong_length (bytes : Slice U8) (length : bytes.val.length ≠ 1880) :
 decodeCall bytes = .ok (.Err .InvalidAccountData) := by
 rw [decode_closed]
 unfold NFY_NEX_PublicModel.run NFY_NEX_TerminalOracle.run
 have bad := NMT_R2_Scalar.slice_wrong_length bytes length
 simp only [NMT_R2_DecodeConstants.terminal_size,
  bind_tc_ok,bad,if_true,mapOuter,mapCore,fromPE]
#print axioms wrong_length
end NMT_R2_DecodeWrongLength
end
