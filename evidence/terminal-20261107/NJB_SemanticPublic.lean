import NIU_COMBINED_IMPORT
import NGK_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NJB_SemanticPublic
open pool_v1.pair_forest_terminal
open pool_v1.pair_forest_semantic_terminal
/-- Exact constructor law for every immutable source statement. No successful
child observation, canonicality or endpoint-equality premise. -/
def value : PoolV1PairForestTerminalStatementV1 → r0.Public
 | .PrivateTransfer common public1 => .Transfer public1 common.lane_transition
 | .Withdrawal common public1 => .Withdrawal public1 common.lane_transition

theorem result (statement : PoolV1PairForestTerminalStatementV1) :
 statement.semantic_public = ok (value statement) := by
 cases statement <;> rfl

#print result
#print axioms result
end AspisR1.NJB_SemanticPublic
