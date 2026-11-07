import NNH_MEntry1Pda
import NNH_MEntry1ValueRSL
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry1PdaValue
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier
attribute [local instance] Classical.propDecidable

theorem value (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV1) :
 outer (reply id) (NNH_MEntry1Pda.run (NNH_MRegistryOps.install base D env) v m.key (unkey D.registry) e t entry) =
 ok (ebind (option (env.pda [RSL.SEED_ENTRY,(key m.key).bytes,RSL.PROFILE_BINDING.bytes,RSL.RELEASE_BINDING.bytes,[byte entry.bump]] D.registry) .invalidAccountData) fun expected =>
  eseq (echeck (decide ((account e).key ≠ expected)) .invalidAccountData)
   (eseq (echeck (RSL.TX2_234.entryV1Bad (NNH_MRegistryArgs.args v p m s r e t) (entryV1 entry)) .invalidAccountData) (.ok ()))) := by
 rw [NNH_MEntry1Pda.source]
 have h := NNH_MPdaTransport.value env (NNH_MPdaSeeds.entry1 m.key entry.bump) (unkey D.registry)
  (NNH_MRegistryEntry1Check.check (NNH_MRegistryOps.install base D env) v m.key e t entry) id
  (fun expected => eseq (echeck (decide ((account e).key ≠ expected)) .invalidAccountData)
   (eseq (echeck (RSL.TX2_234.entryV1Bad (NNH_MRegistryArgs.args v p m s r e t) (entryV1 entry)) .invalidAccountData) (.ok ())))
  (fun expected => NNH_MEntry1ValueRSL.value base D env v p m s r e t entry expected)
 rw [NNH_MPdaSeeds.entry1_bytes,key_forth] at h
 exact h

#print axioms value
end NNH_MEntry1PdaValue
end
