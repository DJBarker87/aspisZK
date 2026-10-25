import S2W_OuterOccurrences
import GExq_RecordTrace
import S2W_NativeConsolidation
set_option autoImplicit false
namespace AspisR1.RawJ_SecondTraceFields
open Aeneas Aeneas.Std Result S2W_Trace _root_.AdapterRw AspisR1.AdapterRw S2W_OuterOccurrences
attribute [local irreducible] _root_.AdapterRw.r1_pool_adapter.owned.validate_asq8

theorem fields (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Cuts.Account) (data : Slice U8)
    (slot : core.result.Result U64 Cuts.PE) (log : Log)
    (execution : run ops (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts data slot)
      [] = ok (.Ok (),log)) : ∃ pa ca raw checkpoint, ∃ (encoded : Array U8 1880#usize), ∃ proof finish,
      Slice.index_usize accounts 0#usize = ok pa ∧
      Slice.index_usize accounts 6#usize = ok ca ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops pa = ok (.Ok raw) ∧
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops ca = ok (.Ok checkpoint) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        raw {start := 688#usize, «end» := finish} = ok proof ∧
      raw.val.length = finish.val ∧
      ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
        (Array.to_slice encoded) proof checkpoint () none = ok (.Ok ()) ∧
      GExq_RecordTrace.projectLog log = [.second (Array.to_slice encoded) proof checkpoint (.Ok ())] := by
  simp only [S2W_Outer.stage2_owned,S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,
    S2W_Outer.traceEffects,run_perform,S2W_Outer.mapError,then_assoc,then_ok, S2W_Trace.bind] at execution
  repeat' first
  | (solve | cases execution)
  | (fail_if_no_progress simp only [S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,run_perform,S2W_Outer.mapError,then_assoc,then_ok, S2W_Trace.bind] at execution)
  | uncase_result
  | head_reduce execution
  | split at execution
  all_goals have logs := congrArg Prod.snd (Result.ok.inj execution)
  all_goals dsimp only at logs
  all_goals rw [← logs]
  all_goals simp only [GExq_RecordTrace.projectLog,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.nil_append,List.append_nil,GExq_OuterRecord.project]
  all_goals simp_all only [S2W_Trace.invoke,
    AdapterRw.Constants.constant_aspis_statement_pool_v1_pair_terminal_POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES]
  all_goals aesop (add simp [bne_iff_ne])

#print axioms fields
end AspisR1.RawJ_SecondTraceFields
