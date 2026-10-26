import S6CurrentFirstInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S6N_Getters
open AdapterRw.aspis_statement.pool_v1
abbrev Statement := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Public := pair_forest_semantic_terminal.r0.Public

def commonValue : Statement → Common
  | .PrivateTransfer common _ => common
  | .Withdrawal common _ => common

def publicValue : Statement → Public
  | .PrivateTransfer common pub => .Transfer pub common.lane_transition
  | .Withdrawal common pub => .Withdrawal pub common.lane_transition

/-- The complete extracted getters are total field projections on both enum
variants. No validator, decoder success or canonicality premise is used. -/
theorem complete (statement : Statement) :
    pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement = ok (commonValue statement) ∧
    pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement = ok (publicValue statement) := by
  cases statement <;> exact ⟨rfl,rfl⟩

/-- Arbitrary continuations retain the same statement and selected public
fields. This is the Aeneas value/borrow model; native pointer checks are separate. -/
theorem contextual {A : Type} (statement : Statement)
    (tail : Common → Public → Statement → Result A) :
    (do let common ← pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common statement
        let pub ← pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public statement
        tail common pub statement) =
      tail (commonValue statement) (publicValue statement) statement := by
  rw [(complete statement).1,(complete statement).2]
  rfl

/-- The source semantic projection is exactly the public carrier consumed by
S6 and Claims. The same statement is retained across the conversion. -/
theorem selected (statement : Statement) :
    AspisS6CurrentVerifierCarrier.toPublic (publicValue statement) =
      AspisR1CurrentCaller.FirstComposition.toCurrentPublic
        (AspisR1PublicPreparation.PreparationBinding.preparationPublic
          (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 statement)) := by
  cases statement <;> rfl

#print axioms complete
#print axioms contextual
#print axioms selected
end AspisR1.S6N_Getters
