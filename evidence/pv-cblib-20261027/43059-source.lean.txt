import R1Z.PV_CBL_FallbackConstantMatrix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant08
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 32#usize = ok 666307205#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 33#usize = ok 773529912#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 34#usize = ok 1294757372#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 35#usize = ok 1396182291#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 8#usize =
    ok PV_CBL_FallbackConstantMatrix.q8 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant08
