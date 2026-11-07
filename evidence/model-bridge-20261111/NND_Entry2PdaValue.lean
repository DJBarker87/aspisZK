import NND_Entry2PdaSource
import NND_Entry2ExpectedValue
set_option autoImplicit false
noncomputable section
namespace NND_Entry2PdaValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned
attribute [local instance] Classical.propDecidable

def tail (env : RSL.Env) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (entry : RSL.EntryV2) : Except RSL.ProgramError Unit :=
 ebind (option (env.pda [RSL.SEED_ENTRY_V2,a.master_account.key.bytes,RSL.PROFILE_BINDING.bytes,RSL.RELEASE_BINDING.bytes,[entry.bump]] D.registry) .invalidAccountData)
  (NND_Entry2ExpectedValue.tail env a entry)

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
 outer (reply id) (NND_Entry2Pda.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID) entry) =
 ok (tail env D (NND_RegistryArgs.args v p m s r e t) (entryV2 entry)) := by
 rw [NND_Entry2PdaSource.source]
 have h := NND_PdaTransport.value env (NND_PdaSeeds.entry2 m.key entry.bump) (unkey D.registry)
  (NND_Entry2Expected.run (NND_RegistryOps.install base D env) v m.key (unkey RSL.LOADER_ID) e t (unkey RSL.LOADER_ID) entry) id
  (NND_Entry2ExpectedValue.tail env (NND_RegistryArgs.args v p m s r e t) (entryV2 entry))
  (fun expected => NND_Entry2ExpectedValue.value base D env v p m s r e t entry expected)
 rw [NND_PdaSeeds.entry2_bytes,key_forth] at h
 exact h

#print axioms value
end NND_Entry2PdaValue
end
