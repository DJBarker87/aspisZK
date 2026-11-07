import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S037
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 37: raw; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount)
 (next : solana_pubkey.Pubkey → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.key checkpointAccount)) next) ()) =
 (r1_pool_adapter.owned.OwnedAccount.impl.key checkpointAccount) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ()) := by
 rw [NMX_StepCore.entered]
 simp only [source]
 rw [NMX_ErasureLaws.continue_raw]
 cases h : r1_pool_adapter.owned.OwnedAccount.impl.key checkpointAccount <;> rfl
#print axioms step
end NMX_S037
end
