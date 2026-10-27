import PoolL_MarkerLengthSource
set_option autoImplicit false
namespace AspisR1.PoolL_MarkerLengthFacts
open Aeneas Aeneas.Std Result PoolL_MarkerLengthSource

theorem exact (data : Slice U8) :
    PoolL_marker_length data =
      (if data.val.length = (208#usize).val then ok (.Ok ())
       else ok (.Err (.Custom 1095966757#u32))) := by
  unfold PoolL_marker_length
  by_cases h : data.val.length = (208#usize).val <;>
    simp [h,Slice.len,
      PoolM_NativeCancelSource.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]
#print axioms exact
end AspisR1.PoolL_MarkerLengthFacts
