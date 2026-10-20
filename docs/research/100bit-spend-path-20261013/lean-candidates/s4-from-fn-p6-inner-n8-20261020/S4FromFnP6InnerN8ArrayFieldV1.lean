import S4FromFnP6InnerN8ConcreteV2
import S4FourDotsP6ArrayOperationV1

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false

namespace AspisR1FromFnP6Generated

/-- A P6-backed field adapter at the generated inner N=8 `arrayFromFn` call.
The original operation remains in force at all other lengths. -/
def fourDotsOpsWithP6ArrayFromFnN8
    (ops : AspisR1FastDotsCurrent.FourDotsOps) :
    AspisR1FastDotsCurrent.FourDotsOps :=
  { ops with
    arrayFromFn := fun {T F} N callback initial =>
      if N.val = 8 then arrayFromFnP6 N callback initial
      else ops.arrayFromFn N callback initial }

/-- Success of the exact generated N=8 operation-field call, with the P6
adapter installed, yields the fixed eight-cell reducer/readback contract. -/
theorem generatedInnerN8ArrayField_success_values_match_fixedV6
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (limbs : fast_dots.four_dots.closure.closure)
    (values : Aeneas.Std.Array Std.U32 8#usize)
    (h : (fourDotsOpsWithP6ArrayFromFnN8 ops).arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (fourDotsOpsWithP6ArrayFromFnN8 ops)) limbs = .ok values) :
    ∃ m0 m1 m2 m3 m4 m5 m6 m7 w0 w1 w2 w3 w4 w5 w6 w7,
      values.val = [m0,m1,m2,m3,m4,m5,m6,m7] ∧
      Array.index_usize limbs 0#usize = .ok w0 ∧ ops.m31ReduceU64 w0 = .ok m0 ∧
      Array.index_usize limbs 1#usize = .ok w1 ∧ ops.m31ReduceU64 w1 = .ok m1 ∧
      Array.index_usize limbs 2#usize = .ok w2 ∧ ops.m31ReduceU64 w2 = .ok m2 ∧
      Array.index_usize limbs 3#usize = .ok w3 ∧ ops.m31ReduceU64 w3 = .ok m3 ∧
      Array.index_usize limbs 4#usize = .ok w4 ∧ ops.m31ReduceU64 w4 = .ok m4 ∧
      Array.index_usize limbs 5#usize = .ok w5 ∧ ops.m31ReduceU64 w5 = .ok m5 ∧
      Array.index_usize limbs 6#usize = .ok w6 ∧ ops.m31ReduceU64 w6 = .ok m6 ∧
      Array.index_usize limbs 7#usize = .ok w7 ∧ ops.m31ReduceU64 w7 = .ok m7 := by
  have hN : (8#usize).val = 8 := by decide
  have hmodel : arrayFromFnP6 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (fourDotsOpsWithP6ArrayFromFnN8 ops)) limbs = .ok values := by
    simpa [fourDotsOpsWithP6ArrayFromFnN8, hN] using h
  exact innerArrayP6_success_values_match_fixedV6
    (fourDotsOpsWithP6ArrayFromFnN8 ops) limbs values hmodel

#print axioms generatedInnerN8ArrayField_success_values_match_fixedV6

end AspisR1FromFnP6Generated
