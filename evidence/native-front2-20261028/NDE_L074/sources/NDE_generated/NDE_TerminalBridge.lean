import NDE_Reference13.Funs
import NDE_LiftBridge
import AdapterRwModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_TerminalBridge
open AdapterRw.aspis_statement.pool_v1
abbrev S := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev P := payment_relation.PoolV1PrivateTransferPublicV1
abbrev W := payment_relation.PoolV1WithdrawalPublicV1
abbrev T := pair_tree_profile.PoolV1PairLatePublicStatementV1
abbrev View := NDE_Reference13.TerminalView P W T

def input : S → View
 | .PrivateTransfer c p => .Transfer p c.lane_transition
 | .Withdrawal c w => .Withdrawal w c.lane_transition

def output : View → pair_forest_semantic_terminal.r0.Public
 | .Transfer p t => .Transfer p t
 | .Withdrawal w t => .Withdrawal w t

theorem selected (cp : core.marker.Copy P) (cw : core.marker.Copy W)
    (ct : core.marker.Copy T) (s : S) :
    NDE_LiftBridge.mapResult output (NDE_Reference13.terminal_view_ref cp cw ct (input s)) =
      pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public s := by
  cases s <;> rfl

#print axioms selected
end NDE_TerminalBridge
