import R1Z.PV_RunJoin_CircleNeutralShape53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralR24Body53
open PV_RunJoin_CircleNeutralShape53
abbrev Q := (U32 × U32) × (U32 × U32)
/-- Guard-free body reification of the selected neutral R72 computation. -/
def body (left right : Q) : Result (Option Q) := do
  let a := left.fst.fst
  let b := left.fst.snd
  let c := left.snd.fst
  let d := left.snd.snd
  let e := right.fst.fst
  let f := right.fst.snd
  let g := right.snd.fst
  let h := right.snd.snd
  let a1 ← lift (UScalar.cast .U64 a)
  let b1 ← lift (UScalar.cast .U64 b)
  let c1 ← lift (UScalar.cast .U64 c)
  let d1 ← lift (UScalar.cast .U64 d)
  let e1 ← lift (UScalar.cast .U64 e)
  let f1 ← lift (UScalar.cast .U64 f)
  let g1 ← lift (UScalar.cast .U64 g)
  let h1 ← lift (UScalar.cast .U64 h)
  let i ← c1 * g1
  let i1 ← PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.PP
  let i2 ← lift (core.num.U64.wrapping_add i i1)
  let i3 ← d1 * h1
  let i4 ← lift (core.num.U64.wrapping_sub i2 i3)
  let u ←
    PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
      () i4
  let i5 ← c1 * h1
  let i6 ← d1 * g1
  let i7 ← lift (core.num.U64.wrapping_add i5 i6)
  let v ←
    PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
      () i7
  let i8 ← a1 * e1
  let i9 ← lift (core.num.U64.wrapping_add i8 i1)
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
  let i27 ← 2#u64 * i1
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


theorem canonical (left right : Q) (hl : QC left) (hr : QC right) :
    PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul left right = body left right := by
  have hleft0 : ¬ left.1.1 ≥ PV_RunJoin_CircleR72Raw52.field.P := Nat.not_le.mpr hl.1.1
  have hleft1 : ¬ left.1.2 ≥ PV_RunJoin_CircleR72Raw52.field.P := Nat.not_le.mpr hl.1.2
  have hleft2 : ¬ left.2.1 ≥ PV_RunJoin_CircleR72Raw52.field.P := Nat.not_le.mpr hl.2.1
  have hleft3 : ¬ left.2.2 ≥ PV_RunJoin_CircleR72Raw52.field.P := Nat.not_le.mpr hl.2.2
  have hright0 : ¬ right.1.1 ≥ PV_RunJoin_CircleR72Raw52.field.P := Nat.not_le.mpr hr.1.1
  have hright1 : ¬ right.1.2 ≥ PV_RunJoin_CircleR72Raw52.field.P := Nat.not_le.mpr hr.1.2
  have hright2 : ¬ right.2.1 ≥ PV_RunJoin_CircleR72Raw52.field.P := Nat.not_le.mpr hr.2.1
  have hright3 : ¬ right.2.2 ≥ PV_RunJoin_CircleR72Raw52.field.P := Nat.not_le.mpr hr.2.2
  unfold PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul
  simp only [if_neg hleft0,if_neg hleft1,if_neg hleft2,if_neg hleft3,if_neg hright0,if_neg hright1,if_neg hright2,if_neg hright3]
  rfl

#print axioms body
#print axioms canonical
end R1Z.PV_RunJoin_CircleNeutralR24Body53
