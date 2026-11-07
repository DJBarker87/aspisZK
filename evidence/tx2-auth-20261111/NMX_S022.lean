import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S022
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 22: raw; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (master : Box Master)
 (next : solana_pubkey.Pubkey → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.fromBytes master.payload.identity.asset_mint)) next) ()) =
 (ops.op37 master.payload.identity.asset_mint) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ()) := by
 rw [NMX_StepCore.entered]
 simp only [source]
 rw [NMX_ErasureLaws.continue_raw]
 cases h : ops.op37 master.payload.identity.asset_mint <;> rfl
#print axioms step
end NMX_S022
end
