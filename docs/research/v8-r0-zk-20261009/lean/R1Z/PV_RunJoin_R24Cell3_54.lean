import R1Z.PV_RunJoin_CircleNeutralR24Tail53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Cell3_54
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
  let i33 ← a1 * h1
  let i34 ← b1 * g1
  let i35 ← lift (core.num.U64.wrapping_add i33 i34)
  let i36 ← c1 * f1
  let i37 ← lift (core.num.U64.wrapping_add i35 i36)
  let i38 ← d1 * e1
  let i39 ← lift (core.num.U64.wrapping_add i37 i38)
  let out3 ← PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 i39
  ok out3
#print axioms cell
end R1Z.PV_RunJoin_R24Cell3_54
