import JHe_NativeAssociation
import JHe_ConfigDigest
import JHe_OriginalSelected
import JHe_TransportCall
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_DeployedChild
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

theorem source (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    verifier.candidate.tx1
      (DrvC_Installation.currentInstalled (JHe_Configuration.value adapter stage))
      (DrvC_Installation.currentDigest (JHe_Configuration.value adapter stage))
      (toCurrentPublic JFs_PublicSerialization.value) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof 10#usize () none=ok (.Ok JHe_WriterSelected.saved) :=
  @JHe_TransportCall.source Unit
    (DrvC_Installation.currentInstalled (JHe_Configuration.value adapter stage))
    {installed with op16:=Tx1Q_Install.writer}
    (DrvC_Installation.currentDigest (JHe_Configuration.value adapter stage)) digest
    (JHe_NativeAssociation.source adapter stage) (JHe_ConfigDigest.source adapter stage)
    () JHe_Run.semantic JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize
    JHe_WriterSelected.saved JHe_OriginalSelected.source
#print axioms source
end AspisR1.JHe_DeployedChild
end
