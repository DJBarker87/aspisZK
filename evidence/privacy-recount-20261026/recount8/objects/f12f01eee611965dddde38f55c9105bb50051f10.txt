import R1Z.ProverRwSuccessNativeWideInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6TransitionSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes]
inductive aspis_statement.pool_v1.pair_forest_semantic_terminal.CompiledVariant
  where
| PrivateTransfer :
  aspis_statement.pool_v1.pair_forest_semantic_terminal.CompiledVariant
| Withdrawal :
  aspis_statement.pool_v1.pair_forest_semantic_terminal.CompiledVariant

structure aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
  where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  recipient_commitment : Array aspis_core.field.M31 8#usize
  change_commitment : Array aspis_core.field.M31 8#usize

structure aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
  where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor_sequence : Std.U64
  anchor_root : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  amount : Std.U32
  destination_token_account : Array Std.U8 32#usize
  change_commitment : Array aspis_core.field.M31 8#usize

structure aspis_statement.pool_v1.pair_forest_semantic_terminal.SemanticPublic
  where
  variant :
    aspis_statement.pool_v1.pair_forest_semantic_terminal.CompiledVariant
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset_id : aspis_core.field.M31
  recipient : Option (Array aspis_core.field.M31 8#usize)
  change : Array aspis_core.field.M31 8#usize
  withdrawal_amount : Option Std.U32
  transition :
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

inductive aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public where
| Transfer :
  aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 →
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 →
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
| Withdrawal :
  aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 →
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 →
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::private_public]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 1327:0-1330:23
    Name pattern: [aspis_statement::pool_v1::pair_forest_semantic_terminal::private_public] -/
@[rust_fun
  "aspis_statement::pool_v1::pair_forest_semantic_terminal::private_public"]
def aspis_statement.pool_v1.pair_forest_semantic_terminal.private_public
  (public1 :
  aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
  (transition1 :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result aspis_statement.pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {
      variant :=
        aspis_statement.pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer,
      pool := public1.pool,
      deployment_domain := public1.deployment_domain,
      anchor := public1.anchor_root,
      nullifier := public1.nullifier,
      asset_id := public1.asset_id,
      recipient := (some public1.recipient_commitment),
      change := public1.change_commitment,
      withdrawal_amount := none,
      transition := transition1
    }

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::withdrawal_public]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 1345:0-1348:23
    Name pattern: [aspis_statement::pool_v1::pair_forest_semantic_terminal::withdrawal_public] -/
@[rust_fun
  "aspis_statement::pool_v1::pair_forest_semantic_terminal::withdrawal_public"]
def aspis_statement.pool_v1.pair_forest_semantic_terminal.withdrawal_public
  (public1 : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
  (transition1 :
  aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result aspis_statement.pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {
      variant :=
        aspis_statement.pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal,
      pool := public1.pool,
      deployment_domain := public1.deployment_domain,
      anchor := public1.anchor_root,
      nullifier := public1.nullifier,
      asset_id := public1.asset_id,
      recipient := none,
      change := public1.change_commitment,
      withdrawal_amount := (some public1.amount),
      transition := transition1
    }

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::semantic]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 2005:8-2005:47
    Name pattern: [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::semantic] -/
@[rust_fun
  "aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::semantic"]
def aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
  (self : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result aspis_statement.pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  match self with
  | aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer
    public1 transition1 =>
    aspis_statement.pool_v1.pair_forest_semantic_terminal.private_public
      public1 transition1
  | aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal
    public1 transition1 =>
    aspis_statement.pool_v1.pair_forest_semantic_terminal.withdrawal_public
      public1 transition1

/-- [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::transition]:
    Source: '/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs', lines 2011:8-2011:70
    Name pattern: [aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::transition]
    Visibility: public -/
@[rust_fun
  "aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::{aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::transition"]
def aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition
  (self : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
  := do
  let sp ←
    aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
      self
  ok sp.transition

/-- [prover_rw_success_direct::transition]:
    Source: 'lib.rs', lines 9:0-9:190
    Visibility: public -/
def transition
  (p : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
  := do
  aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition p

end R1Z.ProverRwP6TransitionSource
