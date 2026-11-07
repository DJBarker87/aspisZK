import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S040
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 40: rust; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (laneAccount : r1_pool_adapter.owned.OwnedAccount)
 (next : Slice U8 → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.data laneAccount)) next) ()) =
 tryThen (r1_pool_adapter.owned.OwnedAccount.data ops laneAccount) (fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ())) := by
 rw [NMX_StepCore.entered]
 exact NMX_ResultSteps.rust ops owners _ _ next
#print axioms step
end NMX_S040
end
