import JHe_NativeAssociation
import JHe_ConfigDigest
import JHe_OriginalCandidate
import JHe_WriterSelected
import JHe_PreparedInventory
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
      JFx_NativeBytes.proof 10#usize () none=ok (.Ok JHe_WriterSelected.saved) := by
  rw [JHe_NativeAssociation.source,JHe_ConfigDigest.source]
  exact JHe_OriginalCandidate.source
    (JGp_Allocation.base (Op5T_Concrete.current JGp_Seeds.base)) true
    JHe_Run.query JHe_Run.geometry JGe_Boundaries.value (NP6_StdModel.calls (.Ok ()))
    digest () JHe_Run.semantic JFx_NativeBytes.publicInput JFx_NativeBytes.proof
    JHe_WriterSelected.saved JHe_PreparedInventory.owner JHe_PreparedInventory.ports
    JHe_WriterSelected.returns
#print axioms source
end AspisR1.JHe_DeployedChild
end
