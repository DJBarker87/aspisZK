import NMT_345Common
import NMT_345Prep_T7
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
abbrev Public := NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public

def semanticValue : Statement → Public
 | .PrivateTransfer c p => .Transfer p c.lane_transition
 | .Withdrawal c p => .Withdrawal p c.lane_transition

def semanticCall (s : Statement) : Result Public :=
 mapOuter NMT_345Prep.fromT5
  (AspisR1PublicPreparation.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
    (NMT_345Prep.toT7 s))
/-- CLOSED268, SAME immutable statement and its full public/transition fields. -/
theorem semantic_closed (s : Statement) : semanticCall s =
 .ok (NMT_345Prep.fromT5 (AspisR1.NJB_SemanticPublic.value (NMT_345Prep.toT7 s))) := by
 unfold semanticCall
 rw [AspisR1.NJB_SemanticPublic.result]
 rfl

theorem semantic_value (s : Statement) : semanticCall s = .ok (semanticValue s) := by
 rw [semantic_closed]
 cases s <;> simp [semanticValue,AspisR1.NJB_SemanticPublic.value,
  NMT_345Prep.toT7,NMT_345Prep.fromT5,NMT_345Prep.toT6,NMT_345Prep.toT4,NMT_345Prep.fromT4]
#print axioms semantic_closed
#print axioms semantic_value
end NMT_345
