import NMT_R2_ReachFull
import NMT_R2_DecodeConstants
import NMT_R2_Scalar
set_option autoImplicit false
noncomputable section
namespace NMT_R2_ReachWrongLength
open Aeneas Aeneas.Std NMT_R2_Reach

theorem source (bytes : Slice U8) (wrong : bytes.val.length ≠ 1880) : reaches bytes = false := by
 unfold reaches full NFY_NEX_TerminalOracle.run
 have bad := NMT_R2_Scalar.slice_wrong_length bytes wrong
 simp only [NMT_R2_DecodeConstants.terminal_size,bind_tc_ok,bad,if_true]
#print axioms source
end NMT_R2_ReachWrongLength
end
