import R1Z.PV_CBL_FallbackConstantMatrix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant15
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 60#usize = ok 2428436474#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 61#usize = ok 2756734187#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 62#usize = ok 3204031479#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 63#usize = ok 3329325298#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 15#usize =
    ok PV_CBL_FallbackConstantMatrix.q15 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant15
