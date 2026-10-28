import NDO_JHg_AuditWorld
import NDO_JGx_SdkInputReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHg_RuntimeInputs
open Aeneas Aeneas.Std Result S2W_D189Wrappers

theorem source (ops : AdapterRw.Ops) (validated : AdapterRw.r1_pool_adapter.ValidatedAsqa) :
    JGx_SdkContinuation.afterValidation ops (JHg_World.e2.second secondSizes) validated =
      JGx_SdkCheckpointRead.afterCheckpoint ops validated JHb_Header.account JFx_NativeBytes.checkpoint :=
  JGx_SdkInputReads.source ops JHg_World.e2 validated JHb_Header.value
    JHg_AuditWorld.proof JHg_AuditWorld.checkpoint
#print axioms source
end AspisR1.JHg_RuntimeInputs
end
