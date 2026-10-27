import JGx_SdkInputReads
import JFv_WorldBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_RuntimeInputs
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers

theorem source (ops : AdapterRw.Ops) (validated : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (headerBytes : Array U8 688#usize) :
    JGx_SdkContinuation.afterValidation ops
      ((JFv_World.e2 (JGx_ProofAccount.value headerBytes)).second secondSizes) validated=
      JGx_SdkCheckpointRead.afterCheckpoint ops validated (JGx_ProofAccount.value headerBytes) JFx_NativeBytes.checkpoint := by
  have inputs := JFv_WorldBytes.inputs (JGx_ProofAccount.value headerBytes)
  exact JGx_SdkInputReads.source ops _ validated headerBytes inputs.2.1 inputs.2.2.2
#print axioms source
end AspisR1.JGx_RuntimeInputs
end
