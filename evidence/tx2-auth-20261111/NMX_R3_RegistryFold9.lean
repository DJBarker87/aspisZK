import NMX_R3_RegistryPda009
import NMX_R3_RegistryFold10
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryFold9
open Aeneas Aeneas.Std AdapterRw NND_Carrier NMX_R3_RegistryEffects

def tail (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (e : RSL.EntryV2) : RSL.RS Unit :=
 RSL.RS.bind (RSL.pdaOrErr
  [RSL.SEED_ENTRY_V2,a.master_account.key.bytes,RSL.PROFILE_BINDING.bytes,RSL.RELEASE_BINDING.bytes,[e.bump]]
  D.registry) (NMX_R3_RegistryFold10.tail a e)

theorem fold (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (reg ent : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (e : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
 RSL.Spec.map (reply id)
  (eval (NMX_R3_RegistryScriptParts.script009 (NMX_R3_RegistryOps.install base D env)
   v ent t (unkey RSL.LOADER_ID) (unkey RSL.LOADER_ID) m.key (unkey D.registry) e)) =
 tail D (NMX_R3_RegistryArgs.args v p m s reg ent t) (entryV2 e) := by
 rw [NMX_R3_RegistryPda009.source]
 apply (NMX_R3_RegistryPdaLaw.fold _ _ _
  (NMX_R3_RegistryFold10.tail (NMX_R3_RegistryArgs.args v p m s reg ent t) (entryV2 e))
  (fun expected => NMX_R3_RegistryFold10.fold base D env v p m s reg ent t e expected)).trans
 simp only [NMX_R3_PdaSeeds.entry2_bytes,key_forth]
 rfl
#print axioms fold
end NMX_R3_RegistryFold9
end
