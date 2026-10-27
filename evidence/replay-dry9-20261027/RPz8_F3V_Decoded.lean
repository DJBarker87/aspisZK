import RPz8_F3V_AllWorldPair
set_option autoImplicit false
namespace AspisR1.F3V_Decoded
open Aeneas Aeneas.Std Result

theorem fields (adapter : AdapterRw.Ops) (pub : Slice U8) (semantic : Port1_Driver.Semantic)
    (success : Port1_Driver.decodeSemantic adapter pub=ok (some semantic)) :
    ∃ statement, adapter.op47 pub=ok (.Ok statement) ∧ adapter.op21 statement=ok (.Ok ()) ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        statement=ok semantic := by
  unfold Port1_Driver.decodeSemantic at success
  repeat' first
    | (solve | cases success)
    | uncase_result
    | head_reduce success
    | split at success
  all_goals cases (Option.some.inj (Result.ok.inj success))
  all_goals exact ⟨_,by assumption,by assumption,by assumption⟩

#print axioms fields
end AspisR1.F3V_Decoded
