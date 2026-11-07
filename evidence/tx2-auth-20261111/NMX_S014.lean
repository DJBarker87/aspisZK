import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S014
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 14: rust; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (masterAccount : r1_pool_adapter.owned.OwnedAccount)
 (next : Slice U8 → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.data masterAccount)) next) ()) =
 tryThen (r1_pool_adapter.owned.OwnedAccount.data ops masterAccount) (fun value => NMX_ValueLink.erase (eval (source ops owners) (next value) ())) := by
 rw [NMX_StepCore.entered]
 exact NMX_ResultSteps.rust ops owners _ _ next
#print axioms step
end NMX_S014
end
