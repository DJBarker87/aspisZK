import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S054
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 54: raw; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (checkpointKey : solana_pubkey.Pubkey)
 (next : Array U8 32#usize → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.toBytes checkpointKey)) next) ()) =
 (ops.op39 checkpointKey) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ()) := by
 rw [NMX_StepCore.entered]
 simp only [source]
 rw [NMX_ErasureLaws.continue_raw]
 cases h : ops.op39 checkpointKey <;> rfl
#print axioms step
end NMX_S054
end
