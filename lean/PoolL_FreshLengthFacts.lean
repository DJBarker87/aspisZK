import PoolL_FreshLengthSource
set_option autoImplicit false
namespace AspisR1.PoolL_FreshLengthFacts
open Aeneas Aeneas.Std Result PoolL_FreshLengthSource

theorem exact (data : Slice U8) (size : Usize) :
    PoolL_fresh_length data size =
      (if data.val.length = (size).val then ok (.Ok ())
       else ok (.Err (.Custom 1095966773#u32))) := by
  unfold PoolL_fresh_length
  by_cases h : data.val.length = (size).val <;>
    simp [h,Slice.len,
      PoolM_NativeCancelSource.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
#print axioms exact
end AspisR1.PoolL_FreshLengthFacts
