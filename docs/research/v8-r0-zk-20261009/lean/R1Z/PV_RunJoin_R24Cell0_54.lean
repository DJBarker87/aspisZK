import R1Z.PV_RunJoin_CircleNeutralR24Tail53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Cell0_54
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
  let i8 ← a1 * e1
  let i9 ← lift (core.num.U64.wrapping_add i8 PV_RunJoin_CircleNeutralR24Leaf53.square)
  let i10 ← b1 * f1
  let i11 ← lift (core.num.U64.wrapping_sub i9 i10)
  let i12 ← 2#u64 * u
  let i13 ← lift (core.num.U64.wrapping_add i11 i12)
  let i14 ← lift (core.convert.num.FromU64U32.from PV_RunJoin_CircleR72Raw52.field.P)
  let i15 ← 3#u64 * i14
  let i16 ← lift (core.num.U64.wrapping_add i13 i15)
  let i17 ← lift (core.num.U64.wrapping_sub i16 v)
  let out0 ← PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 i17
  ok out0
#print axioms cell
end R1Z.PV_RunJoin_R24Cell0_54
