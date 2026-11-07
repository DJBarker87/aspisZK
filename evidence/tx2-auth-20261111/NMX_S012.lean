import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S012
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 12: rust; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (pool : solana_pubkey.Pubkey)
 (laneAccount : r1_pool_adapter.owned.OwnedAccount)
 (next : Unit → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.readonlyAccount laneAccount pool)) next) ()) =
 tryThen (r1_pool_adapter.owned.require_readonly_account ops laneAccount pool) (fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ())) := by
 rw [NMX_StepCore.entered]
 exact NMX_ResultSteps.rust ops owners _ _ next
#print axioms step
end NMX_S012
end
