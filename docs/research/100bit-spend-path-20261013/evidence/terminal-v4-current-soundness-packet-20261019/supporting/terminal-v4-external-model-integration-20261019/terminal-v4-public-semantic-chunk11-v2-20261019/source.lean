import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::withdrawal_public]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1345:0-1361:1 -/
def pool_v1.pair_forest_semantic_terminal.withdrawal_public
  (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
  (transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {
      variant :=
        pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal,
      pool := public1.pool,
      deployment_domain := public1.deployment_domain,
      anchor := public1.anchor_root,
      nullifier := public1.nullifier,
      asset_id := public1.asset_id,
      recipient := none,
      change := public1.change_commitment,
      withdrawal_amount := (some public1.amount),
      transition
    }

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::private_public]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1327:0-1343:1 -/
def pool_v1.pair_forest_semantic_terminal.private_public
  (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
  (transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {
      variant :=
        pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer,
      pool := public1.pool,
      deployment_domain := public1.deployment_domain,
      anchor := public1.anchor_root,
      nullifier := public1.nullifier,
      asset_id := public1.asset_id,
      recipient := (some public1.recipient_commitment),
      change := public1.change_commitment,
      withdrawal_amount := none,
      transition
    }

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::semantic]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2005:8-2010:9 -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  match self with
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer public1 transition
    =>
    pool_v1.pair_forest_semantic_terminal.private_public public1 transition
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal public1
    transition =>
    pool_v1.pair_forest_semantic_terminal.withdrawal_public public1 transition
end AspisR1SelectedMaskProbe
