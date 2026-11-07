import NND_Registry2Pda
set_option autoImplicit false
noncomputable section
namespace NND_Registry2DecodedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV2) : Except RSL.ProgramError Unit :=
 ebind (option (env.pda [RSL.SEED_REGISTRY_V2,a.master_account.key.bytes,[reg.bump]] D.registry) .invalidAccountData)
  (NND_Registry2ExpectedValue.tail L D a env reg)

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) :
 outer (reply id) (NND_RegistryV2Head.decoded (NND_RegistryOps.install base D env) v p m s r e t (unkey D.registry) (unkey RSL.LOADER_ID) reg) =
 ok (tail L D (NND_RegistryArgs.args v p m s r e t) env (registryV2 reg)) := by
 rw [NND_RegistryV2EntryFactor.source,NND_RegistryV2ProgramdataFactor.source,
  NND_RegistryV2ExpectedFactor.source,NND_RegistryV2PdaFactor.source,
  NND_RegistryV2DecodeFactor.source,NND_RegistryV2ReadonlyFactor.source,
  NND_RegistryV2GuardFactor.source,NND_RegistryV2ProgramFactor.source,
  NND_RegistryV2ExpectedFactor2.source,NND_Registry2Pda.source]
 have h := NND_PdaTransport.value env (NND_PdaSeeds.registry2 m.key reg.bump) (unkey D.registry)
  (NND_Registry2Expected.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s r e t reg) id
  (NND_Registry2ExpectedValue.tail L D (NND_RegistryArgs.args v p m s r e t) env (registryV2 reg))
  (fun expected => NND_Registry2ExpectedValue.value base L D env v p m s r e t reg expected)
 rw [NND_PdaSeeds.registry2_bytes,key_forth] at h
 exact h

#print axioms value
end NND_Registry2DecodedValue
end
