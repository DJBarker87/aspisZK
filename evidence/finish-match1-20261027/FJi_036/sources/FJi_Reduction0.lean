import FJi_Grouped0
import FJi_SumBlocks
import JFv_TX2_ScalarMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_Reduction0
open Aeneas Aeneas.Std Result
open FJi_Accumulations
/-- Canonical reduction VALUE after the SAME installed seven-group loop. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (limbs : Sums) (head : NE)
    (loopRun : FIp_NativeDots.fast_dots.four_dots_one_loop0 (JFs_TX2_Iterator.value 0)
      q g slot (Array.repeat 8#usize 0#u64)=ok limbs)
    (finish : JFs_TX2_DotSuffix.scalarFinish limbs=ok head) :
    (JFv_TX2_ArrayMeaning.cell (JFv_TX2_FromLimbsMeaning.limbs head) ⟨0,by decide⟩).val=
      FJi_InnerStep.sum q g slot 0 0 26%2147483647 := by
  rw [JFv_TX2_ScalarMeaning.value limbs head finish ⟨0,by decide⟩,
    ←FJi_OuterTerm.at_fin,FJi_Grouped0.value q g slot limbs loopRun,
    FJi_SumBlocks.source q g slot 0 7 (by decide)]
#print axioms value
end AspisR1.FJi_Reduction0
end
