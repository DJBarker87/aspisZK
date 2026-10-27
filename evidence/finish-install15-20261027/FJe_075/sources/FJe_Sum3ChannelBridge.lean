import FJe_Sum3BridgeBase
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_Sum3ChannelBridge
open Aeneas Aeneas.Std Result
open FJe_Sum3BridgeBase
open FIv_NativeArithmetic (bind_map)
open FIv_PreparedNew (prepared)
abbrev native := FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0
abbrev old := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0
/-- The actual channel traversal shares all integer operands and updates with
its retained checked source,including unsuccessful executions. -/
theorem same (n : Nat) (iter : Range) (a : Left) (s : Sums) (i : Usize)
    (r : Components) (c : Usize) (span : iter.start.val+n=iter.end.val) :
    native iter a s i r c=old iter (left a) s i r c := by
  induction n generalizing iter s with
  | zero =>
    have hn := OccupancyRangeTraversal.next_done iter (by omega)
    rw [native,FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0.eq_def,
      old,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0.eq_def,hn]
    rfl
  | succ n ih =>
    obtain ⟨iter1,hn,hs,he,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    have sp : iter1.start.val+n=iter1.end.val := by rw [he];omega
    have rest := fun s=>ih iter1 s sp
    rw [native,FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0.eq_def,
      old,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0.eq_def,hn]
    simp only [bind_tc_ok,left,FJb_ArrayTransport.index,bind_map,prepared]
    simp only [←left,←native,←old,rest]
#print axioms same
end AspisR1.FJe_Sum3ChannelBridge
end
