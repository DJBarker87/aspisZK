import JFu_PublicProbe
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1

def JFu_serializationProbe : Result (List Nat) := do
  let r ← AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 JFx_NativeBytes.publicInput
  match r with
  | .Err _ => ok []
  | .Ok stmt =>
    let adapter := AspisS6CurrentAdapterCarrier.fromPoolV1PairForestTerminalStatementV1 stmt
    let semantic := S6N_Getters.publicValue adapter
    let retained := AspisR1CurrentCaller.FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic semantic)
    let r ← AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes retained
    match r with
    | .Err _ => ok []
    | .Ok encoded => ok (encoded.val.map UScalar.val)

#eval JFu_serializationProbe
