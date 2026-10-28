import NDO_JHb_WorldBytes
import NDO_JGx_SdkInputReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_RuntimeInputs
open Aeneas Aeneas.Std Result S2W_D189Wrappers

theorem source (ops : AdapterRw.Ops) (validated : AdapterRw.r1_pool_adapter.ValidatedAsqa) :
    JGx_SdkContinuation.afterValidation ops (JHb_World.e2.second secondSizes) validated =
      JGx_SdkCheckpointRead.afterCheckpoint ops validated JHb_Header.account JFx_NativeBytes.checkpoint :=
  JGx_SdkInputReads.source ops JHb_World.e2 validated JHb_Header.value
    JHb_WorldBytes.inputs.2.1 JHb_WorldBytes.inputs.2.2.2
#print axioms source
end AspisR1.JHb_RuntimeInputs
end
