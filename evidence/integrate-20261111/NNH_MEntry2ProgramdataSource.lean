import NNH_MEntry2Programdata
import NNH_MPdaTransport
set_option autoImplicit false
noncomputable section
namespace NNH_MEntry2ProgramdataSource
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned NNH_ModelCarrier

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p loader : solana_pubkey.Pubkey) (t : U64) (a6 : Array U8 32#usize)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
 NNH_MEntry2Programdata.run (NNH_MRegistryOps.install base D env) v p loader t a6 entry =
 NNH_MFormatControl.thenCall (NNH_MRegistryOps.pda env (NNH_MPdaSeeds.programdata v entry.programdata_bump) loader)
  (NNH_MRegistryEntry2Check.check (NNH_MRegistryOps.install base D env) v p t a6 entry) := by
 unfold NNH_MEntry2Programdata.run
 simp only [NNH_MRegistryScalarOps.as_ref,bind_tc_ok,lift]
 unfold NNH_MFormatControl.thenCall NNH_MPdaSeeds.programdata NNH_MPdaSeeds.one
 cases h : env.pda ((NNH_MPdaSeeds.programdata v entry.programdata_bump).val.map bytes) (key loader) <;>
  (simp only [NNH_MRegistryOps.install,NNH_MRegistryOps.pda,NNH_MPdaSeeds.programdata,NNH_MPdaSeeds.one] at h ⊢
   simp only [h,bind_tc_ok]
   rfl)

#print axioms source
end NNH_MEntry2ProgramdataSource
end
