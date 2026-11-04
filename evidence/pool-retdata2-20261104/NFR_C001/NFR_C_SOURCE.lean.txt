import NFO_AcceptedAssociation
import NFO_ResultLayout
import NEY_EmitComposed
set_option autoImplicit false
noncomputable section
namespace NFR_CSettlement
open Aeneas Aeneas.Std Result
abbrev Output := NEU_EmitModel.Output
abbrev Bytes := Array U8 792#usize
abbrev Error := AdapterRw.solana_program_error.ProgramError
abbrev EncodeError := NEU_EmitModel.Error

/-- The deployed Pool error discriminant, not the verifier's generic error. -/
def invalidReturn : Error := .Custom 0x4153202D#u32

inductive Call where
  | validate (value : Output)
  | lane (value : Output)
  | encode (value : Output)

/-- The post-verifier settlement cut. Full child Results are retained; lane
images are arbitrary typed values. It is not the enclosing Pool process. -/
def run {LaneImage : Type}
    (validate : Output → Result (core.result.Result Unit Error))
    (lane : Output → Result (core.result.Result LaneImage Error))
    (encode : Output → Result (core.result.Result Bytes EncodeError))
    (authenticated : NFO_ReadModel.Accepted) :
    Result (core.result.Result (LaneImage × Bytes) Error × List Call) := do
  let result := authenticated.value
  let checked ← validate result
  match checked with
  | .Err e => ok (.Err e,[.validate result])
  | .Ok () =>
    let image ← lane result
    match image with
    | .Err e => ok (.Err e,[.validate result,.lane result])
    | .Ok image =>
      let encoded ← encode result
      match encoded with
      | .Err _ => ok (.Err invalidReturn,[.validate result,.lane result,.encode result])
      | .Ok bytes => ok (.Ok (image,bytes),[.validate result,.lane result,.encode result])

theorem success {LaneImage : Type}
    (validate : Output → Result (core.result.Result Unit Error))
    (lane : Output → Result (core.result.Result LaneImage Error))
    (encode : Output → Result (core.result.Result Bytes EncodeError))
    (authenticated : NFO_ReadModel.Accepted) (image : LaneImage) (bytes : Bytes)
    (checked : validate authenticated.value = ok (.Ok ()))
    (advanced : lane authenticated.value = ok (.Ok image))
    (encoded : encode authenticated.value = ok (.Ok bytes)) :
    run validate lane encode authenticated =
      ok (.Ok (image,bytes),[.validate authenticated.value,.lane authenticated.value,
        .encode authenticated.value]) := by
  simp only [run,checked,advanced,encoded,bind_tc_ok]

theorem rejected_validation {LaneImage : Type}
    (validate : Output → Result (core.result.Result Unit Error))
    (lane : Output → Result (core.result.Result LaneImage Error))
    (encode : Output → Result (core.result.Result Bytes EncodeError))
    (authenticated : NFO_ReadModel.Accepted) (e : Error)
    (rejected : validate authenticated.value = ok (.Err e)) :
    run validate lane encode authenticated = ok (.Err e,[.validate authenticated.value]) := by
  simp only [run,rejected,bind_tc_ok]

theorem rejected_lane {LaneImage : Type}
    (validate : Output → Result (core.result.Result Unit Error))
    (lane : Output → Result (core.result.Result LaneImage Error))
    (encode : Output → Result (core.result.Result Bytes EncodeError))
    (authenticated : NFO_ReadModel.Accepted) (e : Error)
    (checked : validate authenticated.value = ok (.Ok ()))
    (rejected : lane authenticated.value = ok (.Err e)) :
    run validate lane encode authenticated =
      ok (.Err e,[.validate authenticated.value,.lane authenticated.value]) := by
  simp only [run,checked,rejected,bind_tc_ok]

theorem rejected_encoder {LaneImage : Type}
    (validate : Output → Result (core.result.Result Unit Error))
    (lane : Output → Result (core.result.Result LaneImage Error))
    (encode : Output → Result (core.result.Result Bytes EncodeError))
    (authenticated : NFO_ReadModel.Accepted) (image : LaneImage) (e : EncodeError)
    (checked : validate authenticated.value = ok (.Ok ()))
    (advanced : lane authenticated.value = ok (.Ok image))
    (rejected : encode authenticated.value = ok (.Err e)) :
    run validate lane encode authenticated =
      ok (.Err invalidReturn,[.validate authenticated.value,.lane authenticated.value,
        .encode authenticated.value]) := by
  simp only [run,checked,advanced,rejected,bind_tc_ok]

/-- Once the accepted decoder identifies the SAME emitted value, the CLOSED
encoder bridge's domain follows from the original statement validation. No
independent encoder-domain assumption is added at this call edge. -/
theorem reencode_same (s : NEU_EmitModel.Statement)
    (authenticated : NFO_ReadModel.Accepted)
    (same : authenticated.value = AspisR1.S2K.ResultAdmission.value s)
    (valid : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = ok (.Ok ())) :
    NEY_EmitComposed.encode authenticated.value =
      ok (.Ok (AspisR1.S2K.ResultPayload.bytes s)) := by
  rw [same,NEY_EmitComposed.encoder_bridge s]
  exact AspisR1.S2K.ResultPayload.encoded s valid

#print axioms success
#print axioms rejected_validation
#print axioms rejected_lane
#print axioms rejected_encoder
#print axioms reencode_same
end NFR_CSettlement
