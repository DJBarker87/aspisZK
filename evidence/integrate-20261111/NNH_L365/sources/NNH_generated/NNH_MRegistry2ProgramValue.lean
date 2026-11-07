import NNH_MRegistry2ProgramSource
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry2ProgramValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

def tail (L : RSL.PoolLib) (D : RSL.DeployedIds) (a : RSL.TX2_234.Args) (env : RSL.Env)
 (reg : RSL.RegistryV2) : Except RSL.ProgramError Unit :=
 ebind (option (env.pda [D.registry.bytes,[reg.programdata_bump]] RSL.LOADER_ID) .invalidAccountData)
 (NNH_MRegistry2GuardRSL.tail L D a env reg)

theorem value (base : Ops) (L : RSL.PoolLib) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) :
 outer (reply id) (NNH_MRegistry2Program.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s e t reg) =
 ok (tail L D (NNH_MRegistryArgs.args v p m s r e t) env (registryV2 reg)) := by
 rw [NNH_MRegistry2ProgramSource.source]
 have h := NNH_MPdaTransport.value env (NNH_MPdaSeeds.programdata (unkey D.registry) reg.programdata_bump) (unkey RSL.LOADER_ID)
  (NNH_MRegistry2Guard.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) (unkey RSL.LOADER_ID) s e t reg) id
  (NNH_MRegistry2GuardRSL.tail L D (NNH_MRegistryArgs.args v p m s r e t) env (registryV2 reg))
  (fun rpd => NNH_MRegistry2GuardRSL.value base L D env v p m s r e t reg rpd)
 rw [NNH_MPdaSeeds.programdata_bytes,key_forth,key_forth] at h
 exact h

#print axioms value
end NNH_MRegistry2ProgramValue
end
