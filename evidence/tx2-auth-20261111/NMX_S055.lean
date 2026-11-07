import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S055
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 55: raw; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (laneKey : solana_pubkey.Pubkey)
 (next : Array U8 32#usize → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.toBytes laneKey)) next) ()) =
 (ops.op39 laneKey) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ()) := by
 rw [NMX_StepCore.entered]
 simp only [source]
 rw [NMX_ErasureLaws.continue_raw]
 cases h : ops.op39 laneKey <;> rfl
#print axioms step
end NMX_S055
end
