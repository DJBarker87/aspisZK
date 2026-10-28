import NDO_JGb_Sum3Channel
set_option autoImplicit false
namespace AspisR1.JGb_Sum3Component
open Aeneas Aeneas.Std Result
open FIv_PreparedNew (NP prepared)
open JGb_Sum3Channel (Sums Components)
abbrev loop := FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0
abbrev probe := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0

theorem mapped (n : Nat) (it : core.ops.range.Range Usize) (left : Array NP 3#usize)
    (sums : Sums) (index : Usize) (right : Components)
    (span : it.start.val+n=it.end.val) :
    loop it left sums index right=probe it (JGb_ArrayMap.array prepared left) sums index right := by
  induction n generalizing it sums with
  | zero =>
    have hn := ExtractedMaskForwardRange.next_done it (by omega)
    rw [loop,FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0,
      probe,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0]
    simp only [hn,bind_tc_ok,Aeneas.Std.uncurry]
  | succ n ih =>
    obtain ⟨it1,hn,hs,he,_⟩ := ExtractedMaskForwardRange.next_step it (by omega)
    have span1 : it1.start.val+n=it1.end.val := by rw [he,hs];omega
    have recur := fun s => ih it1 s span1
    rw [loop,FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0,
      probe,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0]
    simp only [hn,bind_tc_ok,Aeneas.Std.uncurry]
    have channel := JGb_Sum3Channel.mapped 3 (⟨0#usize,3#usize⟩ : core.ops.range.Range Usize) left sums index right it.start (by rfl)
    change FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0 _ left sums index right it.start = _ at channel
    exact (congrArg (fun (r : Result Sums) => r >>= fun s => loop it1 left s index right) channel).trans
      (by simp only [recur])
#print axioms mapped
end AspisR1.JGb_Sum3Component
