import JHv_Leaves
import JHe_Natives
import JHi_Configuration
import JHf_ReferenceFixed
import JHe_FinalInstallation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_Configuration
open Aeneas Aeneas.Std Result DrvC_Installation

/-- Complete reference selection for the remaining outer fixture operations.
The scan/reconstruction/emitter are existing source bodies, on every input. -/
def adapter (base : AdapterRw.Ops) : AdapterRw.Ops :=
  {JHd_ReferenceSlots.install (JHv_Leaves.install base) with
    op51:=JHf_Scan.source,op52:=JHf_ReconstructionSlot.source,op53:=JHb_EmitAdapter.source}

def seed (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :=
  JHe_Natives.configuration (adapter base) stage

/-- The predecessor validation/wrapper lane uses exactly the TX1 dictionary.
This equality is model configuration coherence, not a native P6 bridge. -/
theorem same (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    JHi_Configuration.value (seed base stage) ()=seed base stage := by
  unfold JHi_Configuration.value JHi_Configuration.base JHf_Configuration.value
    JHf_Configuration.select JHb_EmitInstall.value JGx_CallerSeed.value
    JGx_Configuration.value JGx_Configuration.seed
  change FIp_Install.configuration () (seed base stage) (.Ok ())=seed base stage
  exact JHe_FinalInstallation.source _ _ _
#print axioms same
end AspisR1.JHv_Configuration
end
