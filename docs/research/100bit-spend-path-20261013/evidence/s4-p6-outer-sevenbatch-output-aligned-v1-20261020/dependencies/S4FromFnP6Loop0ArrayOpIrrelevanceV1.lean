import S4FromFnP6OuterSameClosureLoop0V1

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

theorem generatedLoop0_ignores_p6_array_adapter
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (q : Aeneas.Std.Array Std.U8 608#usize)
    (g : Aeneas.Std.Array aspis_core.field.wide_exact.WideExact 29#usize)
    (slot : Usize) (limbs : Aeneas.Std.Array Std.U64 8#usize) :
    fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      (fourDotsOpsWithP6ArrayFromFnN4N8 ops) iter q g slot limbs =
    fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
      ops iter q g slot limbs := by
  rfl

#print axioms generatedLoop0_ignores_p6_array_adapter

end AspisR1FromFnP6Generated
