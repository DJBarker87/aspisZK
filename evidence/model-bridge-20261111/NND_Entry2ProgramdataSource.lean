import NND_Entry2Programdata
import NND_PdaTransport
set_option autoImplicit false
noncomputable section
namespace NND_Entry2ProgramdataSource
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p loader : solana_pubkey.Pubkey) (t : U64) (a6 : Array U8 32#usize)
 (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
 NND_Entry2Programdata.run (NND_RegistryOps.install base D env) v p loader t a6 entry =
 NND_FormatControl.thenCall (NND_RegistryOps.pda env (NND_PdaSeeds.programdata v entry.programdata_bump) loader)
  (NND_RegistryEntry2Check.check (NND_RegistryOps.install base D env) v p t a6 entry) := by
 unfold NND_Entry2Programdata.run
 simp only [NND_RegistryScalarOps.as_ref,bind_tc_ok,lift]
 unfold NND_FormatControl.thenCall NND_PdaSeeds.programdata NND_PdaSeeds.one
 cases h : env.pda ((NND_PdaSeeds.programdata v entry.programdata_bump).val.map bytes) (key loader) <;>
  (simp only [NND_RegistryOps.install,NND_RegistryOps.pda,NND_PdaSeeds.programdata,NND_PdaSeeds.one] at h ⊢
   simp only [h,bind_tc_ok]
   rfl)

#print axioms source
end NND_Entry2ProgramdataSource
end
