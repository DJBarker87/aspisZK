import Aeneas
import RPz7_FIo_Install
import PRVEq_PCVH_R1CandidateWideParserSource_k1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVN_Op2
theorem probe (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : Std.U8) (hl : [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31].length ≤ Usize.max) :
  FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], hl⟩ = ok none := by
  simp [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes, FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN, Slice.len, Slice.index_usize, Aeneas.Std.lift, PCVH.lm, FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs, Array.index_usize, Array.make]
end PCVN_Op2
