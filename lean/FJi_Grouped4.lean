import FJi_OuterValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_Grouped4
open Aeneas Aeneas.Std Result
open FJi_Accumulations
open FJf_U64Array (cell)
/-- Installed coordinate 4, all seven groups, SAME q/g: exact Nat VALUE. -/
theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (out : Sums)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0 (JFs_TX2_Iterator.value 0)
      q g slot (Array.repeat 8#usize 0#u64)=ok out) :
    (cell out 4).val=FJi_OuterStep.sum q g slot 4 7 := by
  exact (FJi_OuterValue.value q g slot out run).2 ⟨4,by decide⟩
#print axioms value
end AspisR1.FJi_Grouped4
end
