import NDO_JGb_ArrayMap
import RPv_FIv_PreparedTotal
import RPv_PoseidonPreparedSum3Source
import ExtractedMaskForwardRange
set_option autoImplicit false
namespace AspisR1.JGb_Sum3Channel
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_PreparedNew (NP prepared)
open FIv_Map (map)
abbrev Sums := Array (Array U64 3#usize) 3#usize
abbrev Components := Array (Array U32 3#usize) 3#usize
abbrev loop := FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0
abbrev probe := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0

theorem mapped (n : Nat) (it : core.ops.range.Range Usize) (left : Array NP 3#usize)
    (sums : Sums) (index : Usize) (right : Components) (component : Usize)
    (span : it.start.val+n=it.end.val) :
    loop it left sums index right component=probe it (JGb_ArrayMap.array prepared left) sums index right component := by
  induction n generalizing it sums with
  | zero =>
    have hn := ExtractedMaskForwardRange.next_done it (by omega)
    rw [loop,FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0,
      probe,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0]
    simp only [hn,bind_tc_ok,Aeneas.Std.uncurry]
  | succ n ih =>
    obtain ⟨it1,hn,hs,he,_⟩ := ExtractedMaskForwardRange.next_step it (by omega)
    have span1 : it1.start.val+n=it1.end.val := by rw [he,hs];omega
    have recur := fun s => ih it1 s span1
    rw [loop,FIq_Native.field.qm31_sum_products3_prepared_loop0_loop0_loop0,
      probe,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0_loop0_loop0]
    simp only [hn,bind_tc_ok,Aeneas.Std.uncurry]
    rw [← JGb_ArrayMap.read prepared left index]
    simp only [FIv_NativeArithmetic.bind_map,prepared,recur]
    rfl
#print axioms mapped
end AspisR1.JGb_Sum3Channel
