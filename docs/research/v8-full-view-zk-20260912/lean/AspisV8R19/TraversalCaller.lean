import AspisR68Circle.Funs
import AspisV8R19.TraversalLaws

/-! Generated eta-closure/model integration, not a Rust normalization theorem.
The two array callers have the exact generated bodies. Library source refinement
and the guarded product's arithmetic correctness remain separate obligations. -/
set_option autoImplicit false
namespace AspisV8R19.TraversalCaller
open Aeneas Aeneas.Std Result AspisR68Circle

theorem left_conversion (x : U32) :
    field.r24_canonical_mul.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut () x =
      .ok (core.convert.num.FromU64U32.from x, ()) := rfl

theorem right_conversion (x : U32) :
    field.r24_canonical_mul.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U64.call_mut () x =
      .ok (core.convert.num.FromU64U32.from x, ()) := rfl

theorem left_array (a b c d : U32) :
    core.array.Array.map
      field.r24_canonical_mul.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
      (Array.make 4#usize [a,b,c,d]) () =
    .ok (Array.make 4#usize [core.convert.num.FromU64U32.from a,
      core.convert.num.FromU64U32.from b,core.convert.num.FromU64U32.from c,
      core.convert.num.FromU64U32.from d]) :=
  TraversalLaws.array_four _ _ _ _ _ _ _ _ _ () () () () () rfl rfl rfl rfl

theorem right_array (a b c d : U32) :
    core.array.Array.map
      field.r24_canonical_mul.closure_2.Insts.CoreOpsFunctionFnMutTupleU32U64
      (Array.make 4#usize [a,b,c,d]) () =
    .ok (Array.make 4#usize [core.convert.num.FromU64U32.from a,
      core.convert.num.FromU64U32.from b,core.convert.num.FromU64U32.from c,
      core.convert.num.FromU64U32.from d]) :=
  TraversalLaws.array_four _ _ _ _ _ _ _ _ _ () () () () () rfl rfl rfl rfl

#print axioms left_conversion
#print axioms right_conversion
#print axioms left_array
#print axioms right_array
-- Audit the entire modeled generated call closure as well as its local lemmas.
#print axioms field.r24_canonical_mul
#print axioms circle.secure_circle_point_from_parameter
#print axioms circle.secure_ood_circle_point_from_parameter
end AspisV8R19.TraversalCaller
