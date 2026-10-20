import AspisR1Post25SamplerStd.Funs

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR1Post25Sampler

namespace AspisR1.ExtractedAddSmallWrapperContractV6

variable [AspisR1Post25Sampler.StdOperationModel]

/-- The source-exact generated add-small wrapper returns the array obtained by
applying its iterator writeback closure to the initial iterator.  The iterator
construction and loop execution remain explicit premises so this lemma does
not assume a model for Rust's standard-library `iter_mut`. -/
theorem add_small_base_p_returns_restored_array
    (digits : Array Std.U32 8#usize) (addend : Std.U32)
    (iter : core.slice.iter.IterMut Std.U32)
    (restore : core.slice.iter.IterMut Std.U32 → Array Std.U32 8#usize)
    (addendOut : Std.U32)
    (back : core.slice.iter.IterMut Std.U32 → core.slice.iter.IterMut Std.U32)
    (hinto :
      AspisR1Post25Sampler.StdOperationModel.into_iter_mut digits =
        .ok (iter, restore))
    (hloop :
      AspisR1Post25Sampler.sampler.add_small_base_p_loop iter
        (fun im => im) addend = .ok (addendOut, back)) :
    AspisR1Post25Sampler.sampler.add_small_base_p digits addend =
      .ok (addendOut != 0#u32, restore (back iter)) := by
  simp [AspisR1Post25Sampler.sampler.add_small_base_p,
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    hinto, hloop]

#print axioms add_small_base_p_returns_restored_array

end AspisR1.ExtractedAddSmallWrapperContractV6
