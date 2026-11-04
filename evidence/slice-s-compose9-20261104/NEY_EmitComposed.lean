import NEX_EmitRuntime
import NEY_BindingSuccess
import NEY_ResultEncoderOracle
import JHb_S2K_ResultPayload
set_option autoImplicit false
noncomputable section
namespace NEY_EmitComposed
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.pair_forest_terminal
open NEU_EmitModel

def encode (record : Output) : Result (core.result.Result Bytes NEU_EmitModel.Error) :=
  NEY_ResultEncoderOracle.run validate_result atomic_statement.encode_digest_canonical
    pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 record

theorem encoder_bridge : EncoderBridge encode := by
  intro s
  exact congrArg (fun value => value.1)
    (NEY_ResultEncoderOracle.result_state_effects (derived s) ())

/-- This reached path condition is derived from binding success on the SAME
statement. It is not a root precondition or a free callee-domain hypothesis. -/
theorem reached_encoder (s : Statement)
    (accepted : validate_pool_v1_pair_forest_terminal_result_against_statement_v1 s
      (derived s)=ok (.Ok ())) :
    validate_pool_v1_pair_forest_terminal_statement_v1 s=ok (.Ok ()) ∧
    encode (derived s)=ok (.Ok (AspisR1.S2K.ResultPayload.bytes s)) := by
  have valid := NEY_BindingSuccess.binding_success s accepted
  refine ⟨valid,?_⟩
  rw [encoder_bridge s]
  exact AspisR1.S2K.ResultPayload.encoded s valid

/-- Kernel MODEL part of the hybrid native certificate. Native source,
call domains and exact ordered return-data arguments require their independent
checked certificates. RuntimeReturnData is ADDED trust under ruling(ab). -/
theorem result_state_effects {A E : Type}
    (state : AspisR1.S2I.ReturnData.State A E) (s : Statement) :
    run validate_pool_v1_pair_forest_terminal_result_against_statement_v1 encode
      (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s =
    AspisR1.JHb_Emit.source (fun st bytes => ok (AspisR1.S2I.ReturnData.set st bytes)) state s :=
  NEX_EmitRuntime.result_state_effects _ encode (fun _ => rfl) encoder_bridge state s

#print axioms encoder_bridge
#print axioms reached_encoder
#print axioms result_state_effects
end NEY_EmitComposed
