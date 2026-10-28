import NDO_JHb_S2K_ResultHeader
import NDO_JFs_PublicValidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_Emit
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
open S2K
/-- Frozen emit_result control flow with an explicit return-data syscall and
its state. Field construction and codecs are the source S2K definitions.
This is a source model; native syscall/artifact association is not asserted. -/
def source {A E : Type}
    (syscall : S2I.ReturnData.State A E → List U8 → Result (S2I.ReturnData.State A E))
    (state : S2I.ReturnData.State A E) (statement : StatementAdmission.Statement) :
    Result (core.result.Result (S2I.ReturnData.State A E) AdapterRw.solana_program_error.ProgramError) := do
  let result := ResultAdmission.value statement
  let validated ← validate_pool_v1_pair_forest_terminal_result_against_statement_v1 statement result
  match validated with
  | .Err _ => ok (.Err .InvalidInstructionData)
  | .Ok () =>
    let encoded ← encode_pool_v1_pair_forest_terminal_result_v1 result
    match encoded with
    | .Err _ => ok (.Err .InvalidInstructionData)
    | .Ok bytes =>
      if bytes.val.length ≠ 792 then ok (.Err .InvalidInstructionData)
      else if bytes.val.take 4 ≠ [65#u8,83#u8,82#u8,56#u8] then ok (.Err .InvalidInstructionData)
      else do
        let state' ← syscall state bytes.val
        ok (.Ok state')

theorem accepted {A E : Type}
    (syscall : S2I.ReturnData.State A E → List U8 → Result (S2I.ReturnData.State A E))
    (runtime : S2I.ReturnData.RuntimePremise syscall)
    (state : S2I.ReturnData.State A E) (statement : StatementAdmission.Statement)
    (valid : validate_pool_v1_pair_forest_terminal_statement_v1 statement=ok (.Ok ())) :
    source syscall state statement=ok (.Ok (S2I.ReturnData.set state (ResultPayload.bytes statement).val)) := by
  unfold source
  dsimp only
  rw [ResultBinding.validated statement valid,bind_tc_ok]
  rw [ResultPayload.encoded statement valid,bind_tc_ok]
  dsimp only
  rw [if_neg (by exact not_not_intro (ResultPayload.bytes statement).property)]
  rw [if_neg (by exact not_not_intro (ResultHeader.magic statement))]
  rw [runtime,bind_tc_ok]
#print axioms accepted

theorem real {A E : Type}
    (syscall : S2I.ReturnData.State A E → List U8 → Result (S2I.ReturnData.State A E))
    (runtime : S2I.ReturnData.RuntimePremise syscall) (state : S2I.ReturnData.State A E) :
    source syscall state JFs_PublicValue.value=
      ok (.Ok (S2I.ReturnData.set state (ResultPayload.bytes JFs_PublicValue.value).val)) :=
  accepted syscall runtime state _ JFs_PublicValidation.source
#print axioms real
end AspisR1.JHb_Emit
end
