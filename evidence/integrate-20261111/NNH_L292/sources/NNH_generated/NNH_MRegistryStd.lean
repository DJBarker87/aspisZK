import NNH_MRegistryReplies
import NGL_CloneDomain
import NGL_ReadonlyModel
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistryStd
open Aeneas Aeneas.Std Result AdapterRw
attribute [local instance] Classical.propDecidable

theorem data (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (a : r1_pool_adapter.owned.OwnedAccount) :
 r1_pool_adapter.owned.OwnedAccount.data (NNH_MRegistryOps.install base D env) a =
 ok (match a.bytes with | .Ok b => .Ok b.deref | .Err e => .Err e) := by
 cases h : a.bytes <;>
 simp only [r1_pool_adapter.owned.OwnedAccount.data,h,NNH_MRegistryOps.install,bind_tc_ok]

theorem readonly (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (a : r1_pool_adapter.owned.OwnedAccount) (p : solana_pubkey.Pubkey) :
 r1_pool_adapter.owned.require_readonly_account (NNH_MRegistryOps.install base D env) a p =
 ok (if !decide (a.owner = p) || a.is_signer || a.is_writable || a.executable
     then .Err .InvalidAccountData else .Ok ()) := by
 exact NGL_ReadonlyModel.owned_result (NNH_MRegistryOps.install base D env) a p

theorem key_ne (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (p q : solana_pubkey.Pubkey) :
 core.cmp.impls.PartialEqShared.ne
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (NNH_MRegistryOps.install base D env)) p q =
 ok (!decide (p=q)) := by
 exact NGL_ReadonlyModel.comparison (NNH_MRegistryOps.install base D env) p q

#print axioms data
#print axioms readonly
#print axioms key_ne
end NNH_MRegistryStd
end
