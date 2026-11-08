import NNV_FinishDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_FinishAt28
open Aeneas Aeneas.Std Result LIB_VCarriers

theorem source (a : K29) :
 (k29Raw a).index_usize 28#usize = .ok (LIB_VScalarCarriers.toRaw (at28 a)) := by
 rw [RawPoseidonExternalRowReads.array_index_usize_ok (k29Raw a) 28#usize (by decide)]
 rfl
#print axioms source
end AspisR1.NNV_FinishAt28
end
