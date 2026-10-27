import RPz7_S6CurrentCodecTotalV1
import RPz7_S6CurrentFirstInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S6N_Decoder
open AspisS6CurrentCodecInstallation AspisS6CurrentAdapterCarrier
open AspisS6OuterNativeOps

/-- Complete wrapper Result, including decoder rejection, fail and divergence.
Safe Box introduction/moves use the existing D188 standard model. -/
theorem complete (bytes : Slice U8) :
    decode bytes = (do
      let reply ← rawDecoder bytes
      match reply with
      | .Ok value => ok (.Ok value)
      | .Err _ => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)) :=
  boxed_eq boxOps bytes

/-- A continuation consumes exactly the returned owned value or exact error. -/
theorem contextual {A : Type} (bytes : Slice U8)
    (next : core.result.Result Statement PE → Result A) :
    (do let value ← decode bytes; next value) =
    (do
      let reply ← rawDecoder bytes
      match reply with
      | .Ok value => next (.Ok value)
      | .Err _ => next (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)) := by
  rw [complete]
  cases rawDecoder bytes with
  | fail e => rfl
  | div => rfl
  | ok r => cases r <;> rfl

/-- Native caller acceptance identifies the decoder value, rather than
postulating an independently successful decoder on the same bytes. -/
theorem accepted_content (bytes : Slice U8) (statement : Statement)
    (accepted : decode bytes = ok (.Ok statement)) :
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes =
      ok (.Ok (toPoolV1PairForestTerminalStatementV1 statement)) :=
  decode_success bytes statement accepted

/-- The wrapper cannot manufacture success on decoder rejection. -/
theorem error (bytes : Slice U8) (e : FormatError)
    (rejected : rawDecoder bytes = ok (.Err e)) :
    decode bytes = ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  rw [complete, rejected]
  rfl

#print axioms complete
#print axioms contextual
#print axioms accepted_content
#print axioms error
end AspisR1.S6N_Decoder
