import FJe_Sum3ChannelBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_Sum3ComponentBridge
open Aeneas Aeneas.Std Result
open FJe_Sum3BridgeBase
abbrev native := FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0
abbrev old := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0
/-- Same three channel-loop calls for each component of the actual inputs. -/
theorem same (n : Nat) (iter : Range) (a : Left) (s : Sums) (i : Usize)
    (r : Components) (span : iter.start.val+n=iter.end.val) :
    native iter a s i r=old iter (left a) s i r := by
  induction n generalizing iter s with
  | zero =>
    have hn := OccupancyRangeTraversal.next_done iter (by omega)
    rw [native,FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0.eq_def,
      old,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0.eq_def,hn]
    rfl
  | succ n ih =>
    obtain ⟨iter1,hn,hs,he,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    have sp : iter1.start.val+n=iter1.end.val := by rw [he];omega
    have rest := fun s=>ih iter1 s sp
    simp only [native,old] at rest
    rw [native,FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0.eq_def,
      old,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0.eq_def,hn]
    change (do
      let sums1 ← FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0
        ⟨0#usize,3#usize⟩ a s i r iter.start
      native iter1 a sums1 i r)=(do
      let sums1 ← AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0
        ⟨0#usize,3#usize⟩ (left a) s i r iter.start
      old iter1 (left a) sums1 i r)
    have hc := FJe_Sum3ChannelBridge.same 3 ⟨0#usize,3#usize⟩ a s i r iter.start (by rfl)
    change FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0 _ _ _ _ _ _=
      AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0 _ _ _ _ _ _ at hc
    rw [hc]
    exact congrArg (fun k=>AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0
      ⟨0#usize,3#usize⟩ (left a) s i r iter.start >>= k)
      (funext (fun next=>ih iter1 next sp))
#print axioms same
end AspisR1.FJe_Sum3ComponentBridge
end
