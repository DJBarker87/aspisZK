import NND_Entry2Pda
import NND_PdaTransport
set_option autoImplicit false
noncomputable section
namespace NND_Entry2PdaSource
open Aeneas Aeneas.Std Result AdapterRw NND_Carrier NND_Returned

theorem source (base : Ops) (D : RSL.DeployedIds) (env : RSL.Env)
 (v p rp loader : solana_pubkey.Pubkey) (e : r1_pool_adapter.owned.OwnedAccount) (t : U64)
 (a6 : Array U8 32#usize) (entry : aspis_statement.pool_v1.verifier_registry.VerifierRegistryEntryV2) :
 NND_Entry2Pda.run (NND_RegistryOps.install base D env) v p rp loader e t a6 entry =
 NND_FormatControl.thenCall (NND_RegistryOps.pda env (NND_PdaSeeds.entry2 p entry.bump) rp)
  (NND_Entry2Expected.run (NND_RegistryOps.install base D env) v p loader e t a6 entry) := by
 unfold NND_Entry2Pda.run
 simp only [NND_RegistryScalarOps.as_ref,bind_tc_ok,lift]
 unfold NND_FormatControl.thenCall NND_PdaSeeds.entry2 NND_PdaSeeds.one
 cases h : env.pda ((NND_PdaSeeds.entry2 p entry.bump).val.map bytes) (key rp) <;>
  (simp only [NND_RegistryOps.install,NND_RegistryOps.pda,NND_PdaSeeds.entry2,NND_PdaSeeds.one] at h ⊢
   simp only [h,bind_tc_ok]
   rfl)

#print axioms source
end NND_Entry2PdaSource
end
