import R1Z.PV_RunJoin_CircleNeutralR24Leaf53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralR24Tail53
abbrev Q := (U32 × U32) × (U32 × U32)
def tail (left right : Q) (u v : U64) : Result (Option Q) := do
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
  let i18 ← a1 * f1
  let i19 ← b1 * e1
  let i20 ← lift (core.num.U64.wrapping_add i18 i19)
  let i21 ← lift (core.num.U64.wrapping_add i20 u)
  let i22 ← 2#u64 * v
  let i23 ← lift (core.num.U64.wrapping_add i21 i22)
  let out1 ← PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 i23
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
  let i33 ← a1 * h1
  let i34 ← b1 * g1
  let i35 ← lift (core.num.U64.wrapping_add i33 i34)
  let i36 ← c1 * f1
  let i37 ← lift (core.num.U64.wrapping_add i35 i36)
  let i38 ← d1 * e1
  let i39 ← lift (core.num.U64.wrapping_add i37 i38)
  let out3 ← PV_RunJoin_CircleR72Raw52.field.M31.reduce_u64 i39
  let c2 ← PV_RunJoin_CircleR72Raw52.field.CM31.new out0 out1
  let c3 ← PV_RunJoin_CircleR72Raw52.field.CM31.new out2 out3
  ok (some { fst := c2, snd := c3 })

#print axioms tail
end R1Z.PV_RunJoin_CircleNeutralR24Tail53
