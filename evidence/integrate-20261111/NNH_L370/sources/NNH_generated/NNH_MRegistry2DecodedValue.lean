import NNH_MRegistry2Pda
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry2DecodedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV2) : Except RSL.ProgramError Unit :=
 ebind (option (env.pda [RSL.SEED_REGISTRY_V2,a.master_account.key.bytes,[reg.bump]] D.registry) .invalidAccountData)
  (NNH_MRegistry2ExpectedValue.tail L D a env reg)

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) :
 outer (reply id) (NNH_MRegistryV2Head.decoded (NNH_MRegistryOps.install base D env) v p m s r e t (unkey D.registry) (unkey RSL.LOADER_ID) reg) =
 ok (tail L D (NNH_MRegistryArgs.args v p m s r e t) env (registryV2 reg)) := by
 rw [NNH_MRegistryV2EntryFactor.source,NNH_MRegistryV2ProgramdataFactor.source,
  NNH_MRegistryV2ExpectedFactor.source,NNH_MRegistryV2PdaFactor.source,
  NNH_MRegistryV2DecodeFactor.source,NNH_MRegistryV2ReadonlyFactor.source,
  NNH_MRegistryV2GuardFactor.source,NNH_MRegistryV2ProgramFactor.source,
  NNH_MRegistryV2ExpectedFactor2.source,NNH_MRegistry2Pda.source]
 have h := NNH_MPdaTransport.value env (NNH_MPdaSeeds.registry2 m.key reg.bump) (unkey D.registry)
  (NNH_MRegistry2Expected.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s r e t reg) id
  (NNH_MRegistry2ExpectedValue.tail L D (NNH_MRegistryArgs.args v p m s r e t) env (registryV2 reg))
  (fun expected => NNH_MRegistry2ExpectedValue.value base L D env v p m s r e t reg expected)
 rw [NNH_MPdaSeeds.registry2_bytes,key_forth] at h
 exact h

#print axioms value
end NNH_MRegistry2DecodedValue
end
