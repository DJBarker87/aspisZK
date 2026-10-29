import R1Z.PV_RunJoin_CircleNeutralR24Tail53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Cell2_54
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
  let i24 ← a1 * g1
  let i25 ← c1 * e1
  let i26 ← lift (core.num.U64.wrapping_add i24 i25)
  let i27 ← 2#u64 * PV_RunJoin_CircleNeutralR24Leaf53.square
  let i28 ← lift (core.num.U64.wrapping_add i26 i27)
  let i29 ← b1 * h1
  let i30 ← lift (core.num.U64.wrapping_sub i28 i29)
  let i31 ← d1 * f1
  let i32 ← lift (core.num.U64.wrapping_sub i30 i31)
  let out2 ← PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 i32
  ok out2
#print axioms cell
end R1Z.PV_RunJoin_R24Cell2_54
