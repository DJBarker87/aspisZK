import S6CurrentAdapterCarrierV1
import S6CurrentBoxedDecoderSourceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6CurrentCodecInstallation
open AspisS6CurrentAdapterCarrier AspisS6OuterNativeOps
abbrev Statement := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev FormatError := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
abbrev PE := AdapterRw.solana_program_error.ProgramError

def mapBoth {A B E F : Type} (value : A → B) (error : E → F) : core.result.Result A E → core.result.Result B F
  | .Ok v => .Ok (value v)
  | .Err e => .Err (error e)

def rawDecoder (bytes : Slice U8) : Result (core.result.Result Statement FormatError) :=
  resultMap (mapBoth fromPoolV1PairForestTerminalStatementV1 fromPoolV1PairForestTerminalFormatErrorV1)
    (AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes)

def boxOps : AspisS6CurrentBoxedDecoderSource.Ops where decode := rawDecoder

def decode (bytes : Slice U8) : Result (core.result.Result Statement PE) :=
  AspisS6CurrentBoxedDecoderSource.decode_public_statement_box boxOps bytes

def encode (statement : Statement) : Result (core.result.Result (Array U8 1880#usize) FormatError) :=
  resultMap (rustMapError fromPoolV1PairForestTerminalFormatErrorV1)
    (AspisS6OuterNativeInstalled.encode (toPoolV1PairForestTerminalStatementV1 statement))

/-- Concrete source-derived codec slots; all other current caller operations
are retained from the supplied installation. This does not instantiate them. -/
def install (ops : AdapterRw.Ops) : AdapterRw.Ops :=
  {ops with op22 := encode,op47 := decode}

theorem boxed_eq (ops : AspisS6CurrentBoxedDecoderSource.Ops) (bytes : Slice U8) :
    AspisS6CurrentBoxedDecoderSource.decode_public_statement_box ops bytes = (do
      let reply ← ops.decode bytes
      match reply with
      | .Ok value => ok (.Ok value)
      | .Err _ => ok (.Err PE.InvalidAccountData)) := by
  unfold AspisS6CurrentBoxedDecoderSource.decode_public_statement_box
  cases run : ops.decode bytes with
  | fail e => simp only [bind_tc_fail]
  | div => simp only [bind_tc_div]
  | ok reply =>
    cases reply <;> simp [AdapterRw.core.result.Result.map_err,
      AspisS6CurrentBoxedDecoderSource.decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError,
      AspisS6CurrentBoxedDecoderSource.decode_public_statement_box.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from]

theorem decode_success (bytes : Slice U8) (statement : Statement)
    (accepted : decode bytes=ok (.Ok statement)) :
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes=
      ok (.Ok (toPoolV1PairForestTerminalStatementV1 statement)) := by
  unfold decode at accepted
  rw [boxed_eq] at accepted
  unfold boxOps rawDecoder at accepted
  cases run : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes with
  | fail e => simp only [run,resultMap,bind_tc_fail] at accepted; cases accepted
  | div => simp only [run,resultMap,bind_tc_div] at accepted; cases accepted
  | ok reply =>
    cases reply with
    | Err e => simp only [run,resultMap,mapBoth,bind_tc_ok] at accepted; cases accepted
    | Ok value =>
      simp only [run,resultMap,mapBoth,bind_tc_ok] at accepted
      cases accepted
      simp only [to_fromPoolV1PairForestTerminalStatementV1]

theorem encode_success (statement : Statement) (encoded : Array U8 1880#usize)
    (accepted : encode statement=ok (.Ok encoded)) :
    AspisS6OuterNativeInstalled.encode (toPoolV1PairForestTerminalStatementV1 statement)=ok (.Ok encoded) := by
  unfold encode at accepted
  cases run : AspisS6OuterNativeInstalled.encode (toPoolV1PairForestTerminalStatementV1 statement) with
  | fail e => simp only [run,resultMap] at accepted; cases accepted
  | div => simp only [run,resultMap] at accepted; cases accepted
  | ok reply =>
    cases reply with
    | Err e => simp only [run,resultMap,rustMapError] at accepted; cases accepted
    | Ok value => simp only [run,resultMap,rustMapError] at accepted; cases accepted; rfl

/-- The exact full-forest accepted roundtrip shape on current caller slots.
Encoder/decoder slots contain concrete source instances, not callbacks assumed
correct. SDK effects and the other Ops fields remain independent obligations. -/
theorem installed_roundtrip (ops : AdapterRw.Ops)
    (original : Slice U8) (statement : Statement) (encoded : Array U8 1880#usize)
    (decoded : (install ops).op47 original=ok (.Ok statement))
    (encoded_actual : (install ops).op22 statement=ok (.Ok encoded)) :
    encoded.val=original.val := by
  exact AspisS6OuterNativeCodec.accepted_roundtrip original
    (toPoolV1PairForestTerminalStatementV1 statement) encoded
    (decode_success original statement decoded) (encode_success statement encoded encoded_actual)

#print axioms boxOps
#print axioms encode
#print axioms boxed_eq
#print axioms decode_success
#print axioms encode_success
#print axioms installed_roundtrip
end AspisS6CurrentCodecInstallation
