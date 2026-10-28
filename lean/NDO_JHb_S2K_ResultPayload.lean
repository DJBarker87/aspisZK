import NDO_JHb_S2K_ResultBinding

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.ResultPayload
open AspisR1TerminalDecoder StatementAdmission StatementChecks ResultAdmission
open pool_v1.pair_forest_terminal

def kindByte : Statement → U8
  | .PrivateTransfer _ _ => 1#u8
  | .Withdrawal _ _ => 2#u8

def bytes (s : Statement) : Array U8 792#usize :=
  ResultEncoding.stores (Array.repeat 792#usize 0#u8)
    (common s).master_account (common s).selected_lane_account
    (DigestBytes.bytes (nullifier s)) (kindByte s) (common s).output_lane
    (AfterstateEncoding.bytes (common s).lane_transition.candidate_afterstate)

theorem encoded (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    encode_pool_v1_pair_forest_terminal_result_v1 (value s) = ok (.Ok (bytes s)) := by
  have valid := ResultAdmission.validated s accepted
  have payload := StatementAdmission.payload s accepted
  have digest := DigestBytes.exact (nullifier s)
  simp only [encode_pool_v1_pair_forest_terminal_result_v1,valid,
    bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [value] at digest payload ⊢
  rw [digest,payload]
  unfold bytes
  generalize Array.repeat 792#usize 0#u8 = output
  cases s <;> simp [value,kind,kindByte,common,nullifier,
    ResultEncoding.stores,POOL_V1_PAIR_FOREST_TERMINAL_RESULT_MAGIC,
    POOL_V1_PAIR_FOREST_TERMINAL_VERSION,pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    RESULT_MASTER_OFFSET,RESULT_SELECTED_LANE_OFFSET,RESULT_NULLIFIER_OFFSET,RESULT_AFTERSTATE_OFFSET,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeFromUsizeSlice,core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    Array.to_slice,Array.from_slice,core.slice.Slice.copy_from_slice,
    Slice.length,Slice.len,Array.update,output.property,List.slice,lift]

  all_goals rfl

#print axioms encoded
end AspisR1.S2K.ResultPayload
