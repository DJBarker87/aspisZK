import NMX_R3_RegistryRun
import NMX_R3_RegistryOps
set_option autoImplicit false
noncomputable section
namespace NMX_R3_RegistryPdaSource
open Aeneas Aeneas.Std AdapterRw NND_Carrier
/-- Runtime/PDA slot: the original byte slices and reply appear unchanged in
one ordered event. The digest/value of the runtime reply is not simulated. -/
theorem source (env : RSL.Env) (aborts : Bool) (s : Slice (Slice U8)) (p : solana_pubkey.Pubkey) :
 NMX_R3_RegistryRun.command env aborts (.pda s p) =
 {NMX_R3_RegistryRun.scalar (NMX_R3_RegistryOps.pda env s p) with
  events := [.pda (s.val.map bytes) (key p) (env.pda (s.val.map bytes) (key p))]} := by
 cases h : env.pda (s.val.map bytes) (key p) <;>
  simp only [NMX_R3_RegistryRun.command,NMX_R3_RegistryOps.pda,h,NMX_R3_RegistryRun.scalar]
#print axioms source
end NMX_R3_RegistryPdaSource
end
