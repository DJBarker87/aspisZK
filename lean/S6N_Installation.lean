import DrvC_Installation
import S6N_Decoder
import S6N_Getters
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.S6N_Installation
open AspisS6CurrentCodecInstallation

/-- Value-level deployment certificate for the actual selected SDK. Native
safe ownership/cleanup is interpreted under D188, with source pins and native
checks in the S6N receipt packet; it is not a new hypothesis of deployed. -/
structure Facts (ops : AdapterRw.Ops) : Prop where
  installed : ops.op47 = decode
  complete : ∀ bytes, ops.op47 bytes = (do
    let reply ← rawDecoder bytes
    match reply with
    | .Ok value => ok (.Ok value)
    | .Err _ => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData))
  total : ∀ bytes, ∃ result, ops.op47 bytes = ok result
  getters : ∀ statement : S6N_Getters.Statement,
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement =
      ok (S6N_Getters.commonValue statement) ∧
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement =
      ok (S6N_Getters.publicValue statement)

/-- Every installed configuration uses the concrete decoder. The free adapter
record does not supply a native/public equality or decoder success premise. -/
theorem facts {F E : Type} (c : DrvC_Installation.Configuration F E) :
    Facts (DrvC_Installation.sdk c) := by
  refine ⟨rfl,?_,?_,S6N_Getters.complete⟩
  · exact S6N_Decoder.complete
  · exact AspisS6CurrentCodecInstallation.decode_total

/-- Applies to the actual source-selected cut statement, preserving the same
public bytes and successful output. No independent decoder witness is chosen. -/
theorem accepted {F E : Type} (c : DrvC_Installation.Configuration F E)
    (bytes : Slice U8) (statement : Statement)
    (run : (DrvC_Installation.sdk c).op47 bytes = ok (.Ok statement)) :
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1 bytes =
      ok (.Ok (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 statement)) ∧
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement =
      ok (S6N_Getters.publicValue statement) := by
  rw [(facts c).installed] at run
  exact ⟨S6N_Decoder.accepted_content bytes statement run,(S6N_Getters.complete statement).2⟩

#print axioms facts
#print axioms accepted
end AspisR1.S6N_Installation
end
