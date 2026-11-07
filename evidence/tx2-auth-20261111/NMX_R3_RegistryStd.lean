import NMX_R3_RegistryOps
import NGL_CloneDomain
import NGL_ReadonlyModel
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryStd
open Aeneas Aeneas.Std Result AdapterRw
attribute [local instance] Classical.propDecidable


theorem readonly (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (a : r1_pool_adapter.owned.OwnedAccount) (p : solana_pubkey.Pubkey) :
 r1_pool_adapter.owned.require_readonly_account (NMX_R3_RegistryOps.install base D env) a p =
 ok (if !decide (a.owner = p) || a.is_signer || a.is_writable || a.executable
     then .Err .InvalidAccountData else .Ok ()) := by
 exact NGL_ReadonlyModel.owned_result (NMX_R3_RegistryOps.install base D env) a p

theorem key_ne (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (p q : solana_pubkey.Pubkey) :
 core.cmp.impls.PartialEqShared.ne
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (NMX_R3_RegistryOps.install base D env)) p q =
 ok (!decide (p=q)) := by
 exact NGL_ReadonlyModel.comparison (NMX_R3_RegistryOps.install base D env) p q

#print axioms readonly
#print axioms key_ne
end NMX_R3_RegistryStd
end
