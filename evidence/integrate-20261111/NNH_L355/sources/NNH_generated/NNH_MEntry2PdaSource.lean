import NNH_MEntry2Pda
import NNH_MPdaTransport
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry2PdaSource
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p rp loader : solana_pubkey.Pubkey) (e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (a6 : Array U8 32#usize) (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
 NNH_MEntry2Pda.run (NNH_MRegistryOps.install base D env) v p rp loader e t a6 entry =
 NNH_MFormatControl.thenCall (NNH_MRegistryOps.pda env (NNH_MPdaSeeds.entry2 p entry.bump) rp)
  (NNH_MEntry2Expected.run (NNH_MRegistryOps.install base D env) v p loader e t a6 entry) := by
 unfold NNH_MEntry2Pda.run
 simp only [NNH_MRegistryScalarOps.as_ref,bind_tc_ok,lift]
 unfold NNH_MFormatControl.thenCall NNH_MPdaSeeds.entry2 NNH_MPdaSeeds.one
 cases h : env.pda ((NNH_MPdaSeeds.entry2 p entry.bump).val.map bytes) (key rp) <;>
  (simp only [NNH_MRegistryOps.install,NNH_MRegistryOps.pda,NNH_MPdaSeeds.entry2,NNH_MPdaSeeds.one] at h ⊢
   simp only [h,bind_tc_ok]
   rfl)

#print axioms source
end NNH_MEntry2PdaSource
end
