import JGx_SdkCheckpointRead
import NDO_JGx_RealEntryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_SdkInputReads
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers

theorem source (ops : AdapterRw.Ops) (entry : Entry)
    (validated : AdapterRw.r1_pool_adapter.ValidatedAsqa) (headerBytes : Array U8 688#usize)
    (proof : entry.buffers (entry.handles 0).1=JGx_ProofAccount.value headerBytes)
    (checkpoint : entry.buffers (entry.handles 6).1=JFx_NativeBytes.checkpoint) :
    JGx_SdkContinuation.afterValidation ops (entry.second secondSizes) validated=
      JGx_SdkCheckpointRead.afterCheckpoint ops validated (JGx_ProofAccount.value headerBytes) JFx_NativeBytes.checkpoint :=
  (JGx_SdkProofRead.source ops _ validated _ _ (JGx_EntryIndices.proof entry)
    (JGx_RealEntryReads.proof ops entry headerBytes proof)).trans
  (JGx_SdkCheckpointRead.source ops _ validated _ _ _ (JGx_EntryIndices.checkpoint entry)
    (JGx_RealEntryReads.checkpoint ops entry checkpoint))
#print axioms source
end AspisR1.JGx_SdkInputReads
end
