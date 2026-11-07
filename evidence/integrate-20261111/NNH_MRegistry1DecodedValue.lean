import NNH_MRegistry1Pda
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry1DecodedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV1) : Except RSL.ProgramError Unit :=
 ebind (option (env.pda [RSL.SEED_REGISTRY,a.master_account.key.bytes,[reg.bump]] D.registry) .invalidAccountData)
  (NNH_MRegistry1GuardRSL.tail L D a env reg)

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) :
 outer (reply id) (NNH_MRegistryV1Head.decoded (NNH_MRegistryOps.install base D env) v p m s r e t (unkey D.registry) reg) =
 ok (tail L D (NNH_MRegistryArgs.args v p m s r e t) env (registryV1 reg)) := by
 rw [NNH_MRegistryV1EntryFactor.source,NNH_MRegistryV1PdaFactor.source,
  NNH_MRegistryV1DecodeFactor.source,NNH_MRegistryV1ReadonlyFactor.source,
  NNH_MRegistryV1GuardFactor.source,NNH_MRegistry1Pda.source]
 have h := NNH_MPdaTransport.value env (NNH_MPdaSeeds.registry1 m.key reg.bump) (unkey D.registry)
  (NNH_MRegistry1Guard.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) s r e t reg) id
  (NNH_MRegistry1GuardRSL.tail L D (NNH_MRegistryArgs.args v p m s r e t) env (registryV1 reg))
  (fun expected => NNH_MRegistry1GuardRSL.value base L D env v p m s r e t reg expected)
 rw [NNH_MPdaSeeds.registry1_bytes,key_forth] at h
 exact h

#print axioms value
end NNH_MRegistry1DecodedValue
end
