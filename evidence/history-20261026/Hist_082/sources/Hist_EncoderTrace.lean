import S2W_OuterOccurrences
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_EncoderTrace
open Aeneas Aeneas.Std Result S2W_Trace
open AspisR1.AdapterRw S2W_OuterOccurrences

/-- A literal caller-argument projection, not an independently chosen pub. -/
def readerPublic : Event → Option (Slice U8)
  | .returned (.op11 _ pub _ _ _ _) _ => some pub
  | _ => none

def readerPublics (log : Log) : List (Slice U8) := log.filterMap readerPublic

attribute [local irreducible] AdapterRw.r1_pool_adapter.owned.validate_asq8

/-- Successful actual source validation/encoder calls pin the public value
recorded at the actual reader invocation in the same outer execution. -/
theorem second_public (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice Cuts.Account) (data : Slice U8) (slot : core.result.Result U64 Cuts.PE)
    (validated : AdapterRw.r1_pool_adapter.ValidatedAsqa) (encoded : Array U8 1880#usize)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program accounts data slot = ok (.Ok validated))
    (encoder : ops.op22 validated.statement = ok (.Ok encoded))
    (log : Log)
    (execution : run ops (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts data slot)
      [] = ok (.Ok (),log)) : readerPublics log = [encoded.to_slice] := by
  simp only [S2W_Outer.stage2_owned,S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,
    S2W_Outer.traceEffects,run_perform,S2W_Outer.mapError,then_assoc,then_ok,S2W_Trace.bind] at execution
  repeat' first
  | (solve | cases execution)
  | (fail_if_no_progress simp only [S2W_TraceFacts.run_bind,run_pure,run_lift,run_liftM,run_perform,
      S2W_Outer.mapError,then_assoc,then_ok,S2W_Trace.bind] at execution)
  | uncase_result
  | head_reduce execution
  | split at execution
  all_goals have logs := congrArg Prod.snd (Result.ok.inj execution)
  all_goals dsimp only at logs
  all_goals rw [← logs]
  all_goals simp only [readerPublics,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
    List.nil_append,List.append_nil,readerPublic]
  all_goals simp_all [S2W_Trace.invoke]

#print axioms second_public
end AspisR1.Hist_EncoderTrace
end
