import JGv_PairMeaning
import JGo_TX2_Partial
import JGv_FlushMeaning
import JGv_DotTotal
import JGv_WeightCells09
set_option autoImplicit false
namespace AspisR1.JGv_Obstruction70
open Aeneas Aeneas.Std Result
/-- The next producing gate is on the SAME query-returned accumulator and
actual flushed slice. Neither a Pair success nor an independently chosen rhs
or flushed weight vector supplies it. -/
def DotGoal (a : AspisR1Stage2.verifier.Accumulator) (flushed : Slice SAQ_WideABI.K) : Prop :=
  SAG_DotClosed.source (JFw_Frames.window 8007 2048)
    (JGo_TX2_Partial.writeback a flushed).weights.deref=ok (.Ok a.rhs)
#print DotGoal
#print axioms AspisR1.JGv_Pair.source
#print axioms AspisR1.JGv_PairMeaning.body
#print axioms AspisR1.JGv_QueryScalars.source
#print axioms AspisR1.JGv_QueryRows.source
#print axioms AspisR1.JGv_FlushMeaning.source
#print axioms AspisR1.JGv_DotTotal.source
#print axioms AspisR1.JGv_WeightCells09.cell39_3
end AspisR1.JGv_Obstruction70
