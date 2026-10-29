import R1Z.PV_RunJoin_CircleNeutralR24Tail53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Cell1_54
abbrev Q := (U32 × U32) × (U32 × U32)
def cell (left right : Q) (u v : U64) : Result U32 := do
  let a1 := UScalar.cast .U64 left.1.1
  let b1 := UScalar.cast .U64 left.1.2
  let c1 := UScalar.cast .U64 left.2.1
  let d1 := UScalar.cast .U64 left.2.2
  let e1 := UScalar.cast .U64 right.1.1
  let f1 := UScalar.cast .U64 right.1.2
  let g1 := UScalar.cast .U64 right.2.1
  let h1 := UScalar.cast .U64 right.2.2
  let i18 ← a1 * f1
  let i19 ← b1 * e1
  let i20 ← lift (core.num.U64.wrapping_add i18 i19)
  let i21 ← lift (core.num.U64.wrapping_add i20 u)
  let i22 ← 2#u64 * v
  let i23 ← lift (core.num.U64.wrapping_add i21 i22)
  let out1 ← PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 i23
  ok out1
#print axioms cell
end R1Z.PV_RunJoin_R24Cell1_54
