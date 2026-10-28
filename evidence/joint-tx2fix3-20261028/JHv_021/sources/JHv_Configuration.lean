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

/-- Pure predecessor outer selection, before the already-proved final installation. -/
def prepare (c : Configuration FIo_Install.W Unit) :=
  JGx_Configuration.seed (JGx_CallerSeed.value (JHf_Configuration.select (JHi_Configuration.base c)))

end AspisR1.JHv_Configuration
end
