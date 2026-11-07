import PCD_FrozenRequest.Funs
import PCD_Request
set_option autoImplicit false
noncomputable section
namespace PCD_RequestEmitter
open Aeneas Aeneas.Std PCD_FrozenRequest
abbrev Error := aspis_statement.pool_v1.pair_forest_terminal.PCD_PoolV1PairForestTerminalFormatErrorV1
abbrev ProgramError := solana_program_error.PCD_ProgramError

def continuation (decoded : Result (core.result.Result SharedRequest AspisR1.NFY_JHd_RequestNative.FormatError)) :
    Result (core.result.Result LocalRequest ProgramError) := do
  let decoded ← decoded
  match decoded with
  | .Err _ => .ok (.Err .InvalidInstructionData)
  | .Ok value => .ok (.Ok (mapRequest value))

/-- Complete actual emitted parent, with its external decoder concretely
installed from the CLOSED NLO packet at the SAME arbitrary input slice. -/
theorem emitted_complete (bytes : Slice U8) :
    pair_forest.decode_terminal_request_box_v1 bytes =
      continuation (NFY_NFD_RequestOracle.runSlice bytes) := by
  unfold pair_forest.decode_terminal_request_box_v1
    PCD_FrozenRequest.aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_v1
    continuation
  cases h : NFY_NFD_RequestOracle.runSlice bytes with
  | ok decoded => cases decoded <;> rfl
  | fail error => rfl
  | div => rfl

/-- The installed emitted body has no recoverable error other than the exact
InvalidInstructionData constructor. Child Err payloads are intentionally erased
by the original map_err, not by a carrier quotient. -/
theorem continuation_error (error : AspisR1.NFY_JHd_RequestNative.FormatError) :
    continuation (.ok (.Err error)) = .ok (.Err .InvalidInstructionData) := rfl

theorem continuation_value (value : SharedRequest) :
    continuation (.ok (.Ok value)) = .ok (.Ok (mapRequest value)) := rfl
#print axioms emitted_complete
#print axioms continuation_error
#print axioms continuation_value
end PCD_RequestEmitter
