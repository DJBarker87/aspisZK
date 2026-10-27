import R1Z.ProverRwFullExternalFuns
import R1Z.PV_CB3_StagedKernel
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op249Staged
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Prospective P6 selection. Row credit requires the separate native gate. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op249 := PV_CB3_StagedSource.staged_reference.gamma}
/-- Complete Result for the owned reference, arbitrary byte arrays. This is
not a claim that the native shipped entry equals the owned reference. -/
theorem op249_reference (ops : ExternalFuns) (block : Array U8 32#usize) :
    (selected ops).op249 block = PV_CB3_StagedSource.staged_reference.gamma block := rfl

theorem op249_kernel (ops : ExternalFuns) (block : Array U8 32#usize) :
    (selected ops).op249 block =
      (do let rank0 ← PV_CB3_StagedSource.staged_reference.words block
          PV_CB3_StagedDecode.decode (PV_CB3_StagedKernel.pipeline rank0)) :=
  PV_CB3_StagedKernel.source block
#print axioms op249_reference
#print axioms op249_kernel
end R1Z.PV_CB3_Op249Staged
