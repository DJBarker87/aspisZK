import AspisR1QueryScan.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
namespace AspisR1QueryScanUnrolled.r0_transcript

theorem query_bound_value : QUERY_BOUND = ok 262144#u32 := by
  unfold QUERY_BOUND
  rfl

theorem query_mask_sub_value : 262144#u32 - 1#u32 = ok 262143#u32 := by
  rfl

theorem query_mask_call_mut_exact
    (c : query_words.closure) (w : Std.U32) :
    query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut c w =
      ok (w &&& 262143#u32, c) := by
  simp [query_words.closure.Insts.CoreOpsFunctionFnMutTupleU32U32.call_mut,
    query_bound_value, query_mask_sub_value, lift]

#print axioms query_bound_value
#print axioms query_mask_sub_value
#print axioms query_mask_call_mut_exact
end AspisR1QueryScanUnrolled.r0_transcript
