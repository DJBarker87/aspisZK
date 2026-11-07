import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S023
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 23: raw; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (mintKey : solana_pubkey.Pubkey)
 (next : Slice U8 → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.asRef mintKey)) next) ()) =
 (ops.op40 mintKey) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ()) := by
 rw [NMX_StepCore.entered]
 simp only [source]
 rw [NMX_ErasureLaws.continue_raw]
 cases h : ops.op40 mintKey <;> rfl
#print axioms step
end NMX_S023
end
