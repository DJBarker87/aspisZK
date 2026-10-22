import AspisR1S9ActualQMMulCutV1.Funs
import S9U64ScalarCompatibilityV1
import R22CanonicalCM31

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ActualCM31CrossGraphV1

private def actualCross
    (x y : AspisR1S9ActualQMMulCutV1.field.CM31) : Result Std.U64 := do
  let i ← lift (core.convert.num.FromU64U32.from x.a)
  let i1 ← lift (core.convert.num.FromU64U32.from x.b)
  let i2 ← lift (Std.U64.wrapping_add i i1)
  let i3 ← lift (core.convert.num.FromU64U32.from y.a)
  let i4 ← lift (core.convert.num.FromU64U32.from y.b)
  let i5 ← lift (Std.U64.wrapping_add i3 i4)
  lift (Std.U64.wrapping_mul i2 i5)

private def toProbeCM (x : AspisR1S9ActualQMMulCutV1.field.CM31) :
    AspisR1Qm31ArithmeticProbe.field.CM31 := ⟨x.a, x.b⟩

/-- The actual emitted cross fragment agrees with the exact R22 wrapping
expression for arbitrary operands. -/
theorem actual_cross_wrapping (x y : AspisR1S9ActualQMMulCutV1.field.CM31) :
    actualCross x y = .ok
      (AspisR1.R22CanonicalCM31.wrappingCross (toProbeCM x) (toProbeCM y)) := by
  unfold actualCross AspisR1.R22CanonicalCM31.wrappingCross
    AspisR1.R22CanonicalCM31.widen toProbeCM
  simp only [lift, bind_tc_ok]
  rw [AspisR1S9U64ScalarCompatibilityV1.u64_wrapping_add_eq_uscalar,
    AspisR1S9U64ScalarCompatibilityV1.u64_wrapping_add_eq_uscalar,
    AspisR1S9U64ScalarCompatibilityV1.u64_wrapping_mul_eq_uscalar]

/-- The generated CM31 multiplication body is exactly its source-shaped
seven-operation graph, with the cross-product isolated as `actualCross`.
This claim does not identify the reducer or assert wrapping/current equality. -/
theorem actual_cm_mul_graph
    (x y : AspisR1S9ActualQMMulCutV1.field.CM31) :
    AspisR1S9ActualQMMulCutV1.field.CM31.mul x y = (do
      let m0 ← AspisR1S9ActualQMMulCutV1.field.M31.mul x.a y.a
      let m1 ← AspisR1S9ActualQMMulCutV1.field.M31.mul x.b y.b
      let cross ← actualCross x y
      let m2 ← AspisR1S9ActualQMMulCutV1.field.M31.reduce_u64 cross
      let low ← AspisR1S9ActualQMMulCutV1.field.M31.sub m0 m1
      let high0 ← AspisR1S9ActualQMMulCutV1.field.M31.sub m2 m0
      let high ← AspisR1S9ActualQMMulCutV1.field.M31.sub high0 m1
      .ok ⟨low, high⟩) := by
  simp only [AspisR1S9ActualQMMulCutV1.field.CM31.mul,
    actualCross, lift, bind_tc_ok, bind_assoc_eq]

#print axioms actual_cross_wrapping
#print axioms actual_cm_mul_graph

end AspisR1S9ActualCM31CrossGraphV1
