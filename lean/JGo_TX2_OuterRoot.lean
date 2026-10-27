import JGo_TX2_Root
import JGo_TX2_OuterRootTools
import AuS1_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_OuterRoot
open Aeneas Aeneas.Std Result

def get (base : VTop_Stages.Ops) : Result (Array U8 32#usize) :=
  JGo_TX2_OuterRootTools.get JFx_NativeBytes.proof
    (AuS1_Install.base base).op15 (AuS1_Install.base base).op14
    (AuS1_Install.base base).unwrap32

/-- Full actual installed offset/read/copy/unwrap return, using the same root
already consumed by the installed BatchGoal. No source buffer is reduced. -/
theorem source (base : VTop_Stages.Ops) : get base=ok JGc_TX2_Obstruction70.folded :=
  JGo_TX2_OuterRootTools.source JFx_NativeBytes.proof (JFw_Frames.window 7751 32)
    JGc_TX2_Obstruction70.folded _ _ _ (by rfl) (by rfl)
    JGo_TX2_Root.read JGo_TX2_Root.array (by rfl)
#print axioms source
end AspisR1.JGo_TX2_OuterRoot
end
