import JHe_Run
import JHe_PreparedInventory
import WAdm_ReferenceRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_ReferenceRun
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

def reference (saved : alloc.vec.Vec U8) (run : JHe_Run.Run saved) :=
  WAdm_ReferenceRun.reference installed true JHe_Run.query JHe_Run.geometry digest ()
    JHe_Run.semantic JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize saved run
    JHe_PreparedInventory.owner JHe_PreparedInventory.ports

/-- The original deployed checkpoint writer returns exactly the SAME vector
as the content writer on the SAME preparation, accumulator and flushed slice. -/
theorem writer (saved : alloc.vec.Vec U8) (run : JHe_Run.Run saved) :
    Tx1Q_Install.writer digest run.p {run.out with weights:=⟨run.flushed.val,run.flushed.property⟩}
      JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved :=
  (reference saved run).writer_call
#print axioms writer
end AspisR1.JHe_ReferenceRun
end
