import FJe_Sum3ComponentBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_Sum3IndexBridge
open Aeneas Aeneas.Std Result
open FJe_Sum3BridgeBase
open FIv_NativeArithmetic (bind_map qm cm)
abbrev native := FIq_Native.field.qm31_sum_products3_prepared_loop0
abbrev old := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0
/-- Same right operand,component construction,and index accumulation. -/
theorem same (n : Nat) (iter : Range) (a : Left) (b : Right) (s : Sums)
    (span : iter.start.val+n=iter.end.val) :
    native iter a b s=old iter (left a) (right b) s := by
  induction n generalizing iter s with
  | zero =>
    have hn := OccupancyRangeTraversal.next_done iter (by omega)
    rw [native,FIq_Native.field.qm31_sum_products3_prepared_loop0.eq_def,
      old,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0.eq_def,hn]
    rfl
  | succ n ih =>
    obtain ⟨iter1,hn,hs,he,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    have sp : iter1.start.val+n=iter1.end.val := by rw [he];omega
    have rest := fun s=>ih iter1 s sp
    simp only [native,old] at rest
    rw [native,FIq_Native.field.qm31_sum_products3_prepared_loop0.eq_def,
      old,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0.eq_def,hn]
    change (Array.index_usize b iter.start >>= _) = _
    simp only [FJb_PairProjection.value,bind_tc_ok,right,FJb_ArrayTransport.index,bind_map,qm,
      ←FIv_NativeCM.add,bind_map]
    simp only [cm,FIv_NativeArithmetic.m31_add]
    simp only [FJe_Sum3ComponentBridge.same 3 ⟨0#usize,3#usize⟩ _ _ _ _ (by rfl),rest]
    rfl
#print axioms same
end AspisR1.FJe_Sum3IndexBridge
end
