import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleR72Raw52
abbrev field.M31 := U32
abbrev field.CM31 := U32 × U32
abbrev field.QM31 := field.CM31 × field.CM31
abbrev circle.SecureCirclePoint := field.QM31 × field.QM31
abbrev circle.CirclePointError := Bool
def circle.CirclePointError.SingularParameter : Bool := false
def circle.CirclePointError.ParameterInCm31Subfield : Bool := true
abbrev field.r24_canonical_mul.closure := Unit
def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

def core.result.Result.map_err
  {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F) (self : core.result.Result T E) (op : O) :
  Result (core.result.Result T F)
  := do
  match self with
  | core.result.Result.Ok t => ok (core.result.Result.Ok t)
  | core.result.Result.Err e =>
    let t ← opsfunctionFnOnceOTupleEFInst.call_once op e
    ok (core.result.Result.Err t)

def field.M31.is_zero (self : field.M31) : Result Bool := do
  ok (self = 0#u32)

def field.CM31.is_zero (self : field.CM31) : Result Bool := do
  let b ← field.M31.is_zero self.fst
  if b
  then field.M31.is_zero self.snd
  else ok false

def field.QM31.is_zero (self : field.QM31) : Result Bool := do
  let b ← field.CM31.is_zero self.fst
  if b
  then field.CM31.is_zero self.snd
  else ok false

def field.P : Std.U32 := 2147483647#u32

def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← self + rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

def field.M31.double (self : field.M31) : Result field.M31 := do
  field.M31.add self self

def field.M31.sub (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← self + field.P
  let s ← i - rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

def field.mul_by_r (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.double x.fst
  let m1 ← field.M31.sub m x.snd
  let m2 ← field.M31.double x.snd
  let m3 ← field.M31.add x.fst m2
  ok { fst := m1, snd := m3 }

def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then x3 - field.P
  else ok x3

def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  if self < field.P
  then
    if rhs < field.P
    then
      let i ← lift (UScalar.cast .U64 self)
      let i1 ← lift (UScalar.cast .U64 rhs)
      let x ← i * i1
      let i2 ← lift (UScalar.cast .U64 field.P)
      let i3 ← lift (x &&& i2)
      let i4 ← x >>> 31#i32
      let s ← i3 + i4
      let i5 ← lift (UScalar.cast .U64 field.P)
      if s >= i5
      then
        let i6 ← lift (UScalar.cast .U64 field.P)
        let i7 ← s - i6
        let i8 ← lift (UScalar.cast .U32 i7)
        ok i8
      else let i6 ← lift (UScalar.cast .U32 s)
           ok i6
    else
      let i ← lift (UScalar.cast .U64 self)
      let i1 ← lift (UScalar.cast .U64 rhs)
      let i2 ← i * i1
      let i3 ← field.reduce_u64 i2
      ok i3
  else
    let i ← lift (UScalar.cast .U64 self)
    let i1 ← lift (UScalar.cast .U64 rhs)
    let i2 ← i * i1
    let i3 ← field.reduce_u64 i2
    ok i3

def field.M31.neg (self : field.M31) : Result field.M31 := do
  if self = 0#u32
  then ok 0#u32
  else let i ← field.P - self
       ok i

def field.CM31.inv_with
  (self : field.CM31) (inverse : field.M31 → Result field.M31) :
  Result field.CM31
  := do
  let m ← field.M31.mul self.fst self.fst
  let m1 ← field.M31.mul self.snd self.snd
  let norm ← field.M31.add m m1
  let inv_norm ← inverse norm
  let m2 ← field.M31.mul self.fst inv_norm
  let m3 ← field.M31.neg self.snd
  let m4 ← field.M31.mul m3 inv_norm
  ok { fst := m2, snd := m4 }

def field.square_n_loop.body
  (iter : core.ops.range.Range Std.Usize) (value : field.M31) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × field.M31)
    field.M31)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done value)
  | some _ =>
    let value1 ← field.M31.mul value value
    ok (cont (iter1, value1))

def field.square_n_loop
  (iter : core.ops.range.Range Std.Usize) (value : field.M31) :
  Result field.M31
  := do
  loop
    (fun (iter1, value1) => field.square_n_loop.body iter1 value1)
    (iter, value)

def field.square_n
  (value : field.M31) (count : Std.Usize) : Result field.M31 := do
  field.square_n_loop { start := 0#usize, «end» := count } value

def field.M31.inv (self : field.M31) : Result field.M31 := do
  massert (self != 0#u32)
  let m ← field.M31.mul self self
  let t2 ← field.M31.mul m self
  let m1 ← field.square_n t2 2#usize
  let t4 ← field.M31.mul m1 t2
  let m2 ← field.square_n t4 4#usize
  let t8 ← field.M31.mul m2 t4
  let m3 ← field.square_n t8 8#usize
  let t16 ← field.M31.mul m3 t8
  let m4 ← field.square_n t16 8#usize
  let t24 ← field.M31.mul m4 t8
  let m5 ← field.square_n t24 4#usize
  let t28 ← field.M31.mul m5 t4
  let m6 ← field.M31.mul t28 t28
  let t29 ← field.M31.mul m6 self
  let t30 ← field.M31.mul t29 t29
  let m7 ← field.M31.mul t30 t30
  field.M31.mul m7 self

def field.CM31.inv (self : field.CM31) : Result field.CM31 := do
  field.CM31.inv_with self (field.M31.inv)

def field.r23_product_u32_bounded
  (left : Std.U64) (right : Std.U64) : Result Std.U64 := do
  let i ← lift (core.convert.num.FromU64U32.from core.num.U32.MAX)
  if left <= i
  then
    let i1 ← lift (core.convert.num.FromU64U32.from core.num.U32.MAX)
    if right <= i1
    then
      let i2 ← lift (UScalar.cast .U32 left)
      let i3 ← lift (core.convert.num.FromU64U32.from i2)
      let i4 ← lift (UScalar.cast .U32 right)
      let i5 ← lift (core.convert.num.FromU64U32.from i4)
      i3 * i5
    else left * right
  else left * right

def field.M31.reduce_u64 (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

def field.CM31.square (self : field.CM31) : Result field.CM31 := do
  let i := self.fst
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.snd
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 ← lift (core.convert.num.FromU64U32.from i)
  let i6 ← lift (core.convert.num.FromU64U32.from field.P)
  let i7 ← i5 + i6
  let i8 ← lift (core.convert.num.FromU64U32.from i2)
  let i9 ← i7 - i8
  let i10 ← field.r23_product_u32_bounded i4 i9
  let m ← field.M31.reduce_u64 i10
  let m1 ← field.M31.mul self.fst self.snd
  let m2 ← field.M31.double m1
  ok { fst := m, snd := m2 }

def field.CM31.mul
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m0 ← field.M31.mul self.fst rhs.fst
  let m1 ← field.M31.mul self.snd rhs.snd
  let i := self.fst
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.snd
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 := rhs.fst
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.snd
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← field.r23_product_u32_bounded i4 i9
  let m2 ← field.M31.reduce_u64 i10
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { fst := m, snd := m4 }

def field.CM31.neg (self : field.CM31) : Result field.CM31 := do
  let m ← field.M31.neg self.fst
  let m1 ← field.M31.neg self.snd
  ok { fst := m, snd := m1 }

def field.CM31.sub
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.sub self.fst rhs.fst
  let m1 ← field.M31.sub self.snd rhs.snd
  ok { fst := m, snd := m1 }

def field.QM31.try_inv (self : field.QM31) : Result (Option field.QM31) := do
  let b ← field.QM31.is_zero self
  if b
  then ok none
  else
    let c ← field.CM31.square self.fst
    let c1 ← field.CM31.square self.snd
    let c2 ← field.mul_by_r c1
    let norm ← field.CM31.sub c c2
    let inverse_norm ← field.CM31.inv norm
    let c3 ← field.CM31.mul self.fst inverse_norm
    let c4 ← field.CM31.neg self.snd
    let c5 ← field.CM31.mul c4 inverse_norm
    ok (some { fst := c3, snd := c5 })

def field.CM31.add
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.add self.fst rhs.fst
  let m1 ← field.M31.add self.snd rhs.snd
  ok { fst := m, snd := m1 }

def field.CM31.double (self : field.CM31) : Result field.CM31 := do
  field.CM31.add self self

def field.QM31.square (self : field.QM31) : Result field.QM31 := do
  let c0_square ← field.CM31.square self.fst
  let c1_square ← field.CM31.square self.snd
  let c ← field.mul_by_r c1_square
  let c1 ← field.CM31.add c0_square c
  let c2 ← field.CM31.mul self.fst self.snd
  let c3 ← field.CM31.double c2
  ok { fst := c1, snd := c3 }

def field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
  (c : field.r24_canonical_mul.closure) (tupled_args : Std.U64) :
  Result Std.U64
  := do
  let i ← lift (core.convert.num.FromU64U32.from field.P)
  let i1 ← lift (tupled_args &&& i)
  let i2 ← tupled_args >>> 31#i32
  ok (core.num.U64.wrapping_add i1 i2)

def field.r24_canonical_mul.PP : Result Std.U64 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (UScalar.cast .U64 field.P)
  i * i1

def field.CM31.new (a : field.M31) (b : field.M31) : Result field.CM31 := do
  ok { fst := a, snd := b }

def field.r24_canonical_mul
  (left : field.QM31) (right : field.QM31) : Result (Option field.QM31) := do
  let a := left.fst.fst
  let b := left.fst.snd
  let c := left.snd.fst
  let d := left.snd.snd
  let e := right.fst.fst
  let f := right.fst.snd
  let g := right.snd.fst
  let h := right.snd.snd
  if a >= field.P
  then ok none
  else
    if b >= field.P
    then ok none
    else
      if c >= field.P
      then ok none
      else
        if d >= field.P
        then ok none
        else
          if e >= field.P
          then ok none
          else
            if f >= field.P
            then ok none
            else
              if g >= field.P
              then ok none
              else
                if h >= field.P
                then ok none
                else
                  let a1 ← lift (UScalar.cast .U64 a)
                  let b1 ← lift (UScalar.cast .U64 b)
                  let c1 ← lift (UScalar.cast .U64 c)
                  let d1 ← lift (UScalar.cast .U64 d)
                  let e1 ← lift (UScalar.cast .U64 e)
                  let f1 ← lift (UScalar.cast .U64 f)
                  let g1 ← lift (UScalar.cast .U64 g)
                  let h1 ← lift (UScalar.cast .U64 h)
                  let i ← c1 * g1
                  let i1 ← field.r24_canonical_mul.PP
                  let i2 ← lift (core.num.U64.wrapping_add i i1)
                  let i3 ← d1 * h1
                  let i4 ← lift (core.num.U64.wrapping_sub i2 i3)
                  let u ←
                    field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
                      () i4
                  let i5 ← c1 * h1
                  let i6 ← d1 * g1
                  let i7 ← lift (core.num.U64.wrapping_add i5 i6)
                  let v ←
                    field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
                      () i7
                  let i8 ← a1 * e1
                  let i9 ← lift (core.num.U64.wrapping_add i8 i1)
                  let i10 ← b1 * f1
                  let i11 ← lift (core.num.U64.wrapping_sub i9 i10)
                  let i12 ← 2#u64 * u
                  let i13 ← lift (core.num.U64.wrapping_add i11 i12)
                  let i14 ← lift (core.convert.num.FromU64U32.from field.P)
                  let i15 ← 3#u64 * i14
                  let i16 ← lift (core.num.U64.wrapping_add i13 i15)
                  let i17 ← lift (core.num.U64.wrapping_sub i16 v)
                  let out0 ← field.M31.reduce_u64 i17
                  let i18 ← a1 * f1
                  let i19 ← b1 * e1
                  let i20 ← lift (core.num.U64.wrapping_add i18 i19)
                  let i21 ← lift (core.num.U64.wrapping_add i20 u)
                  let i22 ← 2#u64 * v
                  let i23 ← lift (core.num.U64.wrapping_add i21 i22)
                  let out1 ← field.M31.reduce_u64 i23
                  let i24 ← a1 * g1
                  let i25 ← c1 * e1
                  let i26 ← lift (core.num.U64.wrapping_add i24 i25)
                  let i27 ← 2#u64 * i1
                  let i28 ← lift (core.num.U64.wrapping_add i26 i27)
                  let i29 ← b1 * h1
                  let i30 ← lift (core.num.U64.wrapping_sub i28 i29)
                  let i31 ← d1 * f1
                  let i32 ← lift (core.num.U64.wrapping_sub i30 i31)
                  let out2 ← field.M31.reduce_u64 i32
                  let i33 ← a1 * h1
                  let i34 ← b1 * g1
                  let i35 ← lift (core.num.U64.wrapping_add i33 i34)
                  let i36 ← c1 * f1
                  let i37 ← lift (core.num.U64.wrapping_add i35 i36)
                  let i38 ← d1 * e1
                  let i39 ← lift (core.num.U64.wrapping_add i37 i38)
                  let out3 ← field.M31.reduce_u64 i39
                  let c2 ← field.CM31.new out0 out1
                  let c3 ← field.CM31.new out2 out3
                  ok (some { fst := c2, snd := c3 })

def field.QM31.mul
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let o ← field.r24_canonical_mul self rhs
  match o with
  | none =>
    let m0 ← field.CM31.mul self.fst rhs.fst
    let m1 ← field.CM31.mul self.snd rhs.snd
    let c ← field.CM31.add self.fst self.snd
    let c1 ← field.CM31.add rhs.fst rhs.snd
    let m2 ← field.CM31.mul c c1
    let c2 ← field.mul_by_r m1
    let c3 ← field.CM31.add m0 c2
    let c4 ← field.CM31.sub m2 m0
    let c5 ← field.CM31.sub c4 m1
    ok { fst := c3, snd := c5 }
  | some result => ok result

def field.QM31.sub
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.sub self.fst rhs.fst
  let c1 ← field.CM31.sub self.snd rhs.snd
  ok { fst := c, snd := c1 }

def field.QM31.add
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.add self.fst rhs.fst
  let c1 ← field.CM31.add self.snd rhs.snd
  ok { fst := c, snd := c1 }

def field.QM31.ONE : field.QM31 :=
  { fst := { fst := 1#u32, snd := 0#u32 }, snd := { fst := 0#u32, snd := 0#u32 } }

def circle.secure_circle_point_from_parameter
  (parameter1 : field.QM31) :
  Result (core.result.Result circle.SecureCirclePoint circle.CirclePointError)
  := do
  let square ← field.QM31.square parameter1
  let q ← field.QM31.add field.QM31.ONE square
  let o ← field.QM31.try_inv q
  let r ←
    core.option.Option.ok_or o circle.CirclePointError.SingularParameter
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let q1 ← field.QM31.sub field.QM31.ONE square
    let q2 ← field.QM31.mul q1 val
    let q3 ← field.QM31.add parameter1 parameter1
    let q4 ← field.QM31.mul q3 val
    ok (core.result.Result.Ok { fst := q2, snd := q4 })
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      circle.SecureCirclePoint (core.convert.FromSame circle.CirclePointError)
      residual

def field.CM31.ZERO : field.CM31 := { fst := 0#u32, snd := 0#u32 }

def field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : field.M31) (other : field.M31) : Result Bool := do
  ok (self = other)

def field.CM31.Insts.CoreCmpPartialEqCM31.eq
  (self : field.CM31) (other : field.CM31) : Result Bool := do
  let b ← field.M31.Insts.CoreCmpPartialEqM31.eq self.fst other.fst
  if b
  then field.M31.Insts.CoreCmpPartialEqM31.eq self.snd other.snd
  else ok false

def circle.secure_ood_circle_point_from_parameter
  (parameter1 : field.QM31) :
  Result (core.result.Result circle.SecureCirclePoint circle.CirclePointError)
  := do
  let r ← circle.secure_circle_point_from_parameter parameter1
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let b ←
      field.CM31.Insts.CoreCmpPartialEqCM31.eq parameter1.snd field.CM31.ZERO
    if b
    then
      ok (core.result.Result.Err
        circle.CirclePointError.ParameterInCm31Subfield)
    else ok (core.result.Result.Ok val)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      circle.SecureCirclePoint (core.convert.FromSame circle.CirclePointError)
      residual

def field.M31.ZERO : field.M31 := 0#u32
#print axioms core.option.Option.ok_or
#print axioms core.result.Result.map_err
#print axioms field.M31.is_zero
#print axioms field.CM31.is_zero
#print axioms field.QM31.is_zero
#print axioms field.P
#print axioms field.M31.add
#print axioms field.M31.double
#print axioms field.M31.sub
#print axioms field.mul_by_r
#print axioms field.reduce_u64
#print axioms field.M31.mul
#print axioms field.M31.neg
#print axioms field.CM31.inv_with
#print axioms field.square_n_loop.body
#print axioms field.square_n_loop
#print axioms field.square_n
#print axioms field.M31.inv
#print axioms field.CM31.inv
#print axioms field.r23_product_u32_bounded
#print axioms field.M31.reduce_u64
#print axioms field.CM31.square
#print axioms field.CM31.mul
#print axioms field.CM31.neg
#print axioms field.CM31.sub
#print axioms field.QM31.try_inv
#print axioms field.CM31.add
#print axioms field.CM31.double
#print axioms field.QM31.square
#print axioms field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call
#print axioms field.r24_canonical_mul.PP
#print axioms field.CM31.new
#print axioms field.r24_canonical_mul
#print axioms field.QM31.mul
#print axioms field.QM31.sub
#print axioms field.QM31.add
#print axioms field.QM31.ONE
#print axioms circle.secure_circle_point_from_parameter
#print axioms field.CM31.ZERO
#print axioms field.M31.Insts.CoreCmpPartialEqM31.eq
#print axioms field.CM31.Insts.CoreCmpPartialEqCM31.eq
#print axioms circle.secure_ood_circle_point_from_parameter
#print axioms field.M31.ZERO
end R1Z.PV_RunJoin_CircleR72Raw52
