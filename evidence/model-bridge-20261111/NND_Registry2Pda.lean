import NND_RegistryV2ExpectedFactor2
import NND_Registry2ExpectedValue
set_option autoImplicit false
noncomputable section
namespace NND_Registry2Pda
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p : solana_pubkey.Pubkey) (m : r1_pool_adapter.owned.OwnedAccount)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (r e : r1_pool_adapter.owned.OwnedAccount) (t : U64) (rp loader : solana_pubkey.Pubkey)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) :
 NND_RegistryV2ExpectedFactor2.run (NND_RegistryOps.install base D env) v p m s r e t rp loader reg =
 NND_FormatControl.thenCall (NND_RegistryOps.pda env (NND_PdaSeeds.registry2 m.key reg.bump) rp)
 (NND_Registry2Expected.run (NND_RegistryOps.install base D env) v m.key rp loader s r e t reg) := by
 unfold NND_RegistryV2ExpectedFactor2.run
 simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,NND_RegistryScalarOps.as_ref,bind_tc_ok,lift]
 unfold NND_FormatControl.thenCall NND_PdaSeeds.registry2 NND_PdaSeeds.one
 cases h : env.pda ((NND_PdaSeeds.registry2 m.key reg.bump).val.map bytes) (key rp) <;>
  (simp only [NND_RegistryOps.install,NND_RegistryOps.pda,NND_PdaSeeds.registry2,NND_PdaSeeds.one] at h ⊢
   simp only [h,bind_tc_ok]
   rfl)

#print axioms source
end NND_Registry2Pda
end
