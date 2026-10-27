import JHe_OriginalCandidate
import JHe_WriterSelected
import JHe_PreparedInventory
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_OriginalSelected
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

theorem source : verifier.candidate.tx1 {installed with op16:=Tx1Q_Install.writer}
    digest JHe_Run.semantic JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=
      ok (.Ok JHe_WriterSelected.saved) :=
  JHe_OriginalCandidate.source
    (JGp_Allocation.base (Op5T_Concrete.current JGp_Seeds.base)) true
    JHe_Run.query JHe_Run.geometry JGe_Boundaries.value (NP6_StdModel.calls (.Ok ()))
    digest () JHe_Run.semantic JFx_NativeBytes.publicInput JFx_NativeBytes.proof
    JHe_WriterSelected.saved JHe_PreparedInventory.owner JHe_PreparedInventory.ports
    JHe_WriterSelected.returns
#print axioms source
end AspisR1.JHe_OriginalSelected
end
