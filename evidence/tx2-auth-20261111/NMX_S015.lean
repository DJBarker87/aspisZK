import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_S015
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps
/-- Source occurrence 15: box_master; SAME typed call operands, all outcome arms.
Intermediate emitted-value/owner erasure support; no native/root credit. -/
theorem step (ops : Ops) (owners : Owners) (masterBytes : Slice U8)
 (master : Box Master)
 (next : Box Master → Program Auth) :
 NMX_ValueLink.erase (eval (source ops owners)
  (NMX_Program.bind (NMX_SourceProgram.call (.master masterBytes)) next) ()) =
 tryThen (ops.op48 masterBytes) (fun value => NMX_ValueLink.erase (eval (source ops owners) (next ⟨owners.master,value⟩) ())) := by
 rw [NMX_StepCore.entered]
 exact NMX_ResultSteps.boxed ops owners _ _ _ next
#print axioms step
end NMX_S015
end
