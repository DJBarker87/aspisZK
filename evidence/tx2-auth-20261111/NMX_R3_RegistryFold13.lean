import NMX_R3_RegistryPda013
import NMX_R3_RegistryFold14
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryFold13
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects

def tail (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (r : RSL.RegistryV1) : RSL.RS Unit :=
 RSL.RS.bind (RSL.pdaOrErr [RSL.SEED_REGISTRY,a.master_account.key.bytes,[r.bump]] D.registry)
  (NMX_R3_RegistryFold14.tail D a r)

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (r : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script013 (NMX_R3_RegistryOps.install base D env)
   v m s reg ent t (unkey D.registry) r)) =
 tail D (NMX_R3_RegistryArgs.args v p m s reg ent t) (registryV1 r) := by
 rw [NMX_R3_RegistryPda013.source]
 apply (NMX_R3_RegistryPdaLaw.fold _ _ _
  (NMX_R3_RegistryFold14.tail D (NMX_R3_RegistryArgs.args v p m s reg ent t) (registryV1 r))
  (fun expected => NMX_R3_RegistryFold14.fold base D env v p m s reg ent t r expected)).trans
 simp only [NMX_R3_PdaSeeds.registry1_bytes,key_forth]
 rfl
#print axioms fold
end NMX_R3_RegistryFold13
end
