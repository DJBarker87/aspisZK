import NDO_JGx_FinishAfterPair
import JGx_FinishCompare
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_FinishDot
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
attribute [local irreducible] JFw_Frames.window

theorem bind_source (a : verifier.Accumulator) (dot : E)
    (call : SAG_DotClosed.source (JFw_Frames.window 8007 2048) a.weights.deref=ok (.Ok dot)) :
    JGx_FinishAfterPair.remaining a=JGx_FinishCompare.tail a dot := by
  unfold JGx_FinishAfterPair.remaining
  rw [call,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl
#print axioms bind_source

theorem source (a : verifier.Accumulator) (next : a.next=22#usize)
    (call : SAG_DotClosed.source (JFw_Frames.window 8007 2048) a.weights.deref=ok (.Ok a.rhs)) :
    JGx_FinishAfterPair.remaining a=ok (.Ok ()) :=
  (bind_source a a.rhs call).trans (JGx_FinishCompare.source a next)
#print axioms source
end AspisR1.JGx_FinishDot
end
