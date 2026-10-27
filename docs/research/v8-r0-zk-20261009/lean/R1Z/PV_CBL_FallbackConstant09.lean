import R1Z.PV_CBL_FallbackConstantMatrix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant09
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 36#usize = ok 1695183700#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 37#usize = ok 1986661051#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 38#usize = ok 2177026350#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 39#usize = ok 2456956037#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 9#usize =
    ok PV_CBL_FallbackConstantMatrix.q9 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant09
