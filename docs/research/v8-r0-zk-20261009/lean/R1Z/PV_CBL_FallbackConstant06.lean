import R1Z.PV_CBL_FallbackConstantMatrix
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackConstant06
set_option autoImplicit false
theorem word0 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 24#usize = ok 2554220882#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word1 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 25#usize = ok 2821834349#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word2 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 26#usize = ok 2952996808#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem word3 : Array.index_usize PV_CBL_FallbackBlock.sha_fallback_consts.K32 27#usize = ok 3210313671#u32 := by
  unfold PV_CBL_FallbackBlock.sha_fallback_consts.K32
  rfl
theorem vector : Array.index_usize PV_CBL_FallbackConstantMatrix.matrix 6#usize =
    ok PV_CBL_FallbackConstantMatrix.q6 := by
  rfl
#print axioms word0
#print axioms word1
#print axioms word2
#print axioms word3
#print axioms vector
end R1Z.PV_CBL_FallbackConstant06
