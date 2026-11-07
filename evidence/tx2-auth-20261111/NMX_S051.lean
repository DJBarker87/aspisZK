import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S051
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 51: raw; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (masterKey : solana_pubkey.Pubkey)
 (next : Array U8 32#usize → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.toBytes masterKey)) next) ()) =
 (ops.op39 masterKey) >>= fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ()) := by
 rw [NMX_StepCore.entered]
 simp only [source]
 rw [NMX_ErasureLaws.continue_raw]
 cases h : ops.op39 masterKey <;> rfl
#print axioms step
end NMX_S051
end
