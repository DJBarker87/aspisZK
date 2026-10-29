import R1Z.PV_RDB2E_FallbackSchedule
import R1Z.PV_RDB2E_FallbackArray4
import R1Z.PV_RDB2E_FallbackScalar

section
-- Unchanged source component R1Z.PV_CBL_FallbackLaneRight
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLaneRight
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 o : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.shl (pack a0 a1 a2 a3) o =
      ok (pack (U32.wrapping_shr a0 o) (U32.wrapping_shr a1 o) (U32.wrapping_shr a2 o) (U32.wrapping_shr a3 o)) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.shl,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneRight

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackLaneLeft
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLaneLeft
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 o : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.shr (pack a0 a1 a2 a3) o =
      ok (pack (U32.wrapping_shl a0 o) (U32.wrapping_shl a1 o) (U32.wrapping_shl a2 o) (U32.wrapping_shl a3 o)) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.shr,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneLeft

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackLaneOr
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLaneOr
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 b0 b1 b2 b3 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.or
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) =
      ok (pack (a0 ||| b0) (a1 ||| b1) (a2 ||| b2) (a3 ||| b3)) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.or,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneOr

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackLaneXor
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLaneXor
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 b0 b1 b2 b3 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.xor
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) =
      ok (pack (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3)) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.xor,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneXor

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackSmallSigma
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

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackLaneLoad
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLaneLoad
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 b0 b1 b2 b3 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.sha256load
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) = ok (pack b3 a0 a1 a2) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.sha256load,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneLoad

end

section
-- Unchanged source component R1Z.PV_CBL_FallbackLaneAdd
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackLaneAdd
open PV_CBL_FallbackArray4
set_option autoImplicit false
theorem shape (a0 a1 a2 a3 b0 b1 b2 b3 : U32) :
    PV_CBL_FallbackSchedule.sha_fallback_reference.add
      (pack a0 a1 a2 a3) (pack b0 b1 b2 b3) =
      ok (pack (U32.wrapping_add a0 b0) (U32.wrapping_add a1 b1) (U32.wrapping_add a2 b2) (U32.wrapping_add a3 b3)) := by
  simp only [PV_CBL_FallbackSchedule.sha_fallback_reference.add,index0,index1,index2,index3,lift,bind_tc_ok]
  rfl
#print axioms shape
end R1Z.PV_CBL_FallbackLaneAdd

end
