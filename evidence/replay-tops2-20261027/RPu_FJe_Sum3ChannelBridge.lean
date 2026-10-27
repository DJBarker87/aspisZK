import RPu_FJe_Sum3ChannelEdges
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
    exact (FJe_Sum3ChannelEdges.native_done iter a s i r c hn).trans
      (FJe_Sum3ChannelEdges.old_done iter a s i r c hn).symm
  | succ n ih =>
    obtain ⟨iter1,hn,hs,he,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    have sp : iter1.start.val+n=iter1.end.val := by rw [he];omega
    exact (FJe_Sum3ChannelEdges.native_step iter iter1 a s i r c iter.start hn).trans
      ((congrArg (FJe_Sum3ChannelStep.step a s i r c iter.start)
        (funext (fun next=>ih iter1 next sp))).trans
          (FJe_Sum3ChannelEdges.old_step iter iter1 a s i r c iter.start hn).symm)
#print axioms same
end AspisR1.FJe_Sum3ChannelBridge
end
