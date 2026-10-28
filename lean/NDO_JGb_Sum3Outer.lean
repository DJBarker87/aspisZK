import NDO_JGb_Sum3Component
set_option autoImplicit false
namespace AspisR1.JGb_Sum3Outer
open Aeneas Aeneas.Std Result
open FIv_PreparedNew (NP prepared)
open FIv_NativeArithmetic (NQ qm cm bind_map m31_add)
open JGb_Sum3Channel (Sums)
abbrev loop := FIq_Native.field.qm31_sum_products3_prepared_loop0
abbrev probe := AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0

theorem mapped (n : Nat) (it : core.ops.range.Range Usize) (left : Array NP 3#usize)
    (right : Array NQ 3#usize) (sums : Sums)
    (span : it.start.val+n=it.end.val) :
    loop it left right sums=probe it (JGb_ArrayMap.array prepared left) (JGb_ArrayMap.array qm right) sums := by
  induction n generalizing it sums with
  | zero =>
    have hn := ExtractedMaskForwardRange.next_done it (by omega)
    rw [loop,FIq_Native.field.qm31_sum_products3_prepared_loop0,
      probe,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0]
    simp only [hn,bind_tc_ok,Aeneas.Std.uncurry]
  | succ n ih =>
    obtain ⟨it1,hn,hs,he,_⟩ := ExtractedMaskForwardRange.next_step it (by omega)
    have span1 : it1.start.val+n=it1.end.val := by rw [he,hs];omega
    have recur := fun s => ih it1 s span1
    rw [loop,FIq_Native.field.qm31_sum_products3_prepared_loop0,
      probe,AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared_loop0]
    simp only [hn,bind_tc_ok,Aeneas.Std.uncurry]
    rw [← JGb_ArrayMap.read qm right it.start]
    simp only [FIv_NativeArithmetic.bind_map,qm,cm,← FIv_NativeCM.add,m31_add]
    simp only [JGb_Sum3Component.mapped 3 (⟨0#usize,3#usize⟩ : core.ops.range.Range Usize) left _ _ _ (by rfl),recur]
    simp only [FIq_Native.field.CM31.add,AspisR1SelectedMaskProbe.field.CM31.add,
      m31_add,bind_assoc_eq,bind_tc_ok]
#print axioms mapped
end AspisR1.JGb_Sum3Outer
