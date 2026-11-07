import NNH_MRegistryV2ExpectedFactor2
import NNH_MRegistry2ExpectedValue
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry2Pda
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp loader : solana_pubkey.Pubkey)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) :
 NNH_MRegistryV2ExpectedFactor2.run (NNH_MRegistryOps.install base D env) v p m s r e t rp loader reg =
 NNH_MFormatControl.thenCall (NNH_MRegistryOps.pda env (NNH_MPdaSeeds.registry2 m.key reg.bump) rp)
 (NNH_MRegistry2Expected.run (NNH_MRegistryOps.install base D env) v m.key rp loader s r e t reg) := by
 unfold NNH_MRegistryV2ExpectedFactor2.run
 simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,NNH_MRegistryScalarOps.as_ref,bind_tc_ok,lift]
 unfold NNH_MFormatControl.thenCall NNH_MPdaSeeds.registry2 NNH_MPdaSeeds.one
 cases h : env.pda ((NNH_MPdaSeeds.registry2 m.key reg.bump).val.map bytes) (key rp) <;>
  (simp only [NNH_MRegistryOps.install,NNH_MRegistryOps.pda,NNH_MPdaSeeds.registry2,NNH_MPdaSeeds.one] at h ⊢
   simp only [h,bind_tc_ok]
   rfl)

#print axioms source
end NNH_MRegistry2Pda
end
