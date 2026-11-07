import NND_Registry2ProgramSource
set_option autoImplicit false
noncomputable section
namespace NND_Registry2ProgramValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV2) : Except RSL.ProgramError Unit :=
 ebind (option (env.pda [D.registry.bytes,[reg.programdata_bump]] RSL.LOADER_ID) .invalidAccountData)
 (NND_Registry2GuardRSL.tail L D a env reg)

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) :
 outer (reply id) (NND_Registry2Program.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s e t reg) =
 ok (tail L D (NND_RegistryArgs.args v p m s r e t) env (registryV2 reg)) := by
 rw [NND_Registry2ProgramSource.source]
 have h := NND_PdaTransport.value env (NND_PdaSeeds.programdata (unkey D.registry) reg.programdata_bump) (unkey RSL.LOADER_ID)
  (NND_Registry2Guard.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s e t reg) id
  (NND_Registry2GuardRSL.tail L D (NND_RegistryArgs.args v p m s r e t) env (registryV2 reg))
  (fun rpd => NND_Registry2GuardRSL.value base L D env v p m s r e t reg rpd)
 rw [NND_PdaSeeds.programdata_bytes,key_forth,key_forth] at h
 exact h

#print axioms value
end NND_Registry2ProgramValue
end
