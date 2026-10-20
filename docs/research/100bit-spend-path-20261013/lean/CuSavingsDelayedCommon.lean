import AspisR1DelayedDots.Funs
set_option autoImplicit false
namespace AspisR1.CuSavingsDelayedCommon
open Aeneas Aeneas.Std Result AspisR1DelayedDots
variable [Shared]

theorem base_eq (iter : core.ops.range.Range Usize) (s : Slice U8)
    (a : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (sums : Array U64 8#usize) :
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
      iter s a slot sums =
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
      iter s a slot sums := by rfl

theorem tail_eq (iter : core.ops.range.Range Usize) (s : Slice U8)
    (a : Array field.wide_exact.WideExact 29#usize) (slot : Usize)
    (tail : fast_pairing.EbyKDot) :
    new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
      iter s a slot tail =
    old_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
      iter s a slot tail := by rfl

#print axioms base_eq
#print axioms tail_eq
end AspisR1.CuSavingsDelayedCommon
