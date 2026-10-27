import R1Z.PV_CBL_FallbackLaneRight
import R1Z.PV_CBL_FallbackLaneLeft
import R1Z.PV_CBL_FallbackLaneOr
import R1Z.PV_CBL_FallbackLaneXor
import R1Z.PV_CBL_FallbackScalar
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackSmallSigma
open PV_CBL_FallbackArray4
set_option autoImplicit false
abbrev small0 (x : U32) : U32 :=
  ((U32.wrapping_shr x 7#u32) ||| (U32.wrapping_shl x 25#u32)) ^^^
  ((U32.wrapping_shr x 18#u32) ||| (U32.wrapping_shl x 14#u32)) ^^^
  U32.wrapping_shr x 3#u32
abbrev small1 (x : U32) : U32 :=
  core.num.U32.rotate_right x 17#u32 ^^^ core.num.U32.rotate_right x 19#u32 ^^^ U32.wrapping_shr x 10#u32
theorem sigma0_shape (a b c d : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg1.sigma0x4 (pack a b c d) =
      ok (pack (small0 a) (small0 b) (small0 c) (small0 d)) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.sha256msg1.sigma0x4,
    PV_CBL_FallbackLaneRight.shape,PV_CBL_FallbackLaneLeft.shape,
    PV_CBL_FallbackLaneOr.shape,PV_CBL_FallbackLaneXor.shape,lift,bind_tc_ok]

#print axioms small0
#print axioms small1
#print axioms sigma0_shape
end R1Z.PV_CBL_FallbackSmallSigma
