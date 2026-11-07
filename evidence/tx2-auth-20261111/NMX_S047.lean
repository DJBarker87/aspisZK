import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S047
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 47: pda; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (pool : solana_pubkey.Pubkey)
 (laneSeeds : Slice (Slice U8))
 (next : solana_pubkey.Pubkey → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.pda laneSeeds pool)) next) ()) =
 tryThen (do let reply ← ops.op38 laneSeeds pool; match reply with | .Ok key => ok (.Ok key) | .Err _ => ok (.Err .InvalidAccountData)) (fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ())) := by
 rw [NMX_StepCore.entered]
 exact NMX_ResultSteps.rust ops owners _ _ next
#print axioms step
end NMX_S047
end
