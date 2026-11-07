import NNH_MRegistry2Program
import NNH_MRegistry2GuardRSL
set_option autoImplicit false
noncomputable section
namespace NNH_MRegistry2ProgramSource
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v mk rp loader : solana_pubkey.Pubkey)
 (s : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (reg : aspis_statement.pool_v1.verifier_registry.VerifierRegistryV2) :
 NNH_MRegistry2Program.run (NNH_MRegistryOps.install base D env) v mk rp loader s e t reg =
 NNH_MFormatControl.thenCall (NNH_MRegistryOps.pda env (NNH_MPdaSeeds.programdata rp reg.programdata_bump) loader)
 (NNH_MRegistry2Guard.run (NNH_MRegistryOps.install base D env) v mk rp loader s e t reg) := by
 unfold NNH_MRegistry2Program.run
 simp only [NNH_MRegistryScalarOps.as_ref,bind_tc_ok,lift]
 unfold NNH_MFormatControl.thenCall NNH_MPdaSeeds.programdata NNH_MPdaSeeds.one
 cases h : env.pda ((NNH_MPdaSeeds.programdata rp reg.programdata_bump).val.map bytes) (key loader) <;>
  (simp only [NNH_MRegistryOps.install,NNH_MRegistryOps.pda,NNH_MPdaSeeds.programdata,NNH_MPdaSeeds.one] at h ⊢
   simp only [h,bind_tc_ok]
   rfl)

#print axioms source
end NNH_MRegistry2ProgramSource
end
