import NND_Registry1Pda
set_option autoImplicit false
noncomputable section
namespace NND_Registry1DecodedValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV1) : Except RSL.ProgramError Unit :=
 ebind (option (env.pda [RSL.SEED_REGISTRY,a.master_account.key.bytes,[reg.bump]] D.registry) .invalidAccountData)
  (NND_Registry1GuardRSL.tail L D a env reg)

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV1) :
 outer (reply id) (NND_RegistryV1Head.decoded (NND_RegistryOps.install base D env) v p m s r e t (unkey D.registry) reg) =
 ok (tail L D (NND_RegistryArgs.args v p m s r e t) env (registryV1 reg)) := by
 rw [NND_RegistryV1EntryFactor.source,NND_RegistryV1PdaFactor.source,
  NND_RegistryV1DecodeFactor.source,NND_RegistryV1ReadonlyFactor.source,
  NND_RegistryV1GuardFactor.source,NND_Registry1Pda.source]
 have h := NND_PdaTransport.value env (NND_PdaSeeds.registry1 m.key reg.bump) (unkey D.registry)
  (NND_Registry1Guard.run (NND_RegistryOps.install base D env) v m.key (unkey D.registry) s r e t reg) id
  (NND_Registry1GuardRSL.tail L D (NND_RegistryArgs.args v p m s r e t) env (registryV1 reg))
  (fun expected => NND_Registry1GuardRSL.value base L D env v p m s r e t reg expected)
 rw [NND_PdaSeeds.registry1_bytes,key_forth] at h
 exact h

#print axioms value
end NND_Registry1DecodedValue
end
