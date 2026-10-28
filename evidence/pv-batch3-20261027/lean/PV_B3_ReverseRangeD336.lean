import Aeneas.Std
namespace PV_B3_ReverseRangeD336
open Aeneas Aeneas.Std Result
set_option autoImplicit false
abbrev Iter := core.iter.adapters.rev.Rev (core.ops.range.Range Usize)
def iter (n : Usize) : Iter := { iter := { start := 0#usize, «end» := n } }
def next (n : Usize) : Result (Option Usize × Iter) :=
  core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) (iter n)
#print core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
#print core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back
#print core.iter.range.StepUsize
#print core.iter.range.UScalarStep.backward_checked

theorem sub_value (x y : Usize) (h : y.val ≤ x.val) :
    (Usize.wrapping_sub x y).val = x.val - y.val := by
  rw [Usize.wrapping_sub_val_eq]
  have hx := x.hSize
  have hy := y.hSize
  have shift : x.val + (UScalar.size .Usize - y.val) =
      (x.val - y.val) + UScalar.size .Usize := by omega
  rw [shift, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem next_source (n : Usize) : next n =
    if 0#usize < n then
      ok (some (Usize.wrapping_sub n 1#usize), iter (Usize.wrapping_sub n 1#usize))
    else ok (none, iter n) := by
  simp only [next, iter, core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator, core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize, core.iter.range.UScalarStep,
    core.cmp.impls.PartialOrdUsize.lt, liftFun2,
    core.iter.range.UScalarStep.backward_checked, lift, bind_tc_ok,
    show (0#usize).val = 0 from rfl, show (1#usize).val = 1 from rfl]
  by_cases hn : 0 < n.val
  · have hr : 0#usize < n := hn
    have hb : decide (0 < n.val) = true := by simpa only [decide_eq_true_eq] using hn
    have hs : 1 ≤ n.val := by omega
    rw [if_pos hb, dif_pos hs, if_pos hr]
    simp only [bind_tc_ok]
    congr 4 <;> scalar_tac
  · have hr : ¬ 0#usize < n := hn
    have hb : ¬ decide (0 < n.val) = true := by simpa only [decide_eq_true_eq] using hn
    rw [if_neg hb, if_neg hr]
    rfl

#print axioms iter
#print axioms next
#print axioms sub_value
#print axioms next_source
end PV_B3_ReverseRangeD336
