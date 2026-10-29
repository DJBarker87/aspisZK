import R1Z.PV_RunJoin_CircleRawScalar52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleRawTower52
abbrev field.M31 := U32
abbrev field.CM31 := U32 × U32
abbrev field.QM31 := field.CM31 × field.CM31
abbrev field.P := PV_RunJoin_CircleRawScalar52.field.P
abbrev field.ct.subtract_p := PV_RunJoin_CircleRawScalar52.field.ct.subtract_p
abbrev field.ct.reduce64 := PV_RunJoin_CircleRawScalar52.field.ct.reduce64
abbrev field.ct.add := PV_RunJoin_CircleRawScalar52.field.ct.add
abbrev field.ct.sub := PV_RunJoin_CircleRawScalar52.field.ct.sub
abbrev field.ct.neg := PV_RunJoin_CircleRawScalar52.field.ct.neg
abbrev field.ct.is_zero := PV_RunJoin_CircleRawScalar52.field.ct.is_zero
abbrev field.M31.Insts.CoreCmpPartialEqM31.eq := PV_RunJoin_CircleRawScalar52.field.M31.Insts.CoreCmpPartialEqM31.eq
abbrev field.reduce_u64 := PV_RunJoin_CircleRawScalar52.field.reduce_u64
abbrev field.M31.mul := PV_RunJoin_CircleRawScalar52.field.M31.mul
abbrev field.square_n_loop.body := PV_RunJoin_CircleRawScalar52.field.square_n_loop.body
abbrev field.square_n_loop := PV_RunJoin_CircleRawScalar52.field.square_n_loop
abbrev field.square_n := PV_RunJoin_CircleRawScalar52.field.square_n
abbrev field.M31.reduce_u64 := PV_RunJoin_CircleRawScalar52.field.M31.reduce_u64
abbrev field.M31.add := PV_RunJoin_CircleRawScalar52.field.M31.add
abbrev field.M31.double := PV_RunJoin_CircleRawScalar52.field.M31.double
abbrev field.M31.inv := PV_RunJoin_CircleRawScalar52.field.M31.inv
abbrev field.M31.sub := PV_RunJoin_CircleRawScalar52.field.M31.sub
abbrev field.M31.neg := PV_RunJoin_CircleRawScalar52.field.M31.neg
abbrev field.M31.is_zero := PV_RunJoin_CircleRawScalar52.field.M31.is_zero
def field.CM31.Insts.CoreCmpPartialEqCM31.eq
  (self : field.CM31) (other : field.CM31) :
  Result Bool
  := do
  let b ← field.M31.Insts.CoreCmpPartialEqM31.eq self.fst other.fst
  if b
  then field.M31.Insts.CoreCmpPartialEqM31.eq self.snd other.snd
  else ok false

def field.CM31.ZERO : field.CM31 :=
  { fst := 0#u32, snd := 0#u32 }

def field.CM31.ONE : field.CM31 :=
  { fst := 1#u32, snd := 0#u32 }

def field.CM31.new
  (a : field.M31) (b : field.M31) :
  Result field.CM31
  := do
  ok { fst := a, snd := b }

def field.CM31.add
  (self : field.CM31) (rhs : field.CM31) :
  Result field.CM31
  := do
  let m ← field.M31.add self.fst rhs.fst
  let m1 ← field.M31.add self.snd rhs.snd
  ok { fst := m, snd := m1 }

def field.CM31.sub
  (self : field.CM31) (rhs : field.CM31) :
  Result field.CM31
  := do
  let m ← field.M31.sub self.fst rhs.fst
  let m1 ← field.M31.sub self.snd rhs.snd
  ok { fst := m, snd := m1 }

def field.CM31.neg
  (self : field.CM31) : Result field.CM31 := do
  let m ← field.M31.neg self.fst
  let m1 ← field.M31.neg self.snd
  ok { fst := m, snd := m1 }

def field.CM31.mul
  (self : field.CM31) (rhs : field.CM31) :
  Result field.CM31
  := do
  let m0 ← field.M31.mul self.fst rhs.fst
  let m1 ← field.M31.mul self.snd rhs.snd
  let i := self.fst
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.snd
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← lift (Std.U64.wrapping_add i1 i3)
  let i5 := rhs.fst
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.snd
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← lift (Std.U64.wrapping_add i6 i8)
  let i10 ← lift (Std.U64.wrapping_mul i4 i9)
  let m2 ← field.M31.reduce_u64 i10
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { fst := m, snd := m4 }

def field.CM31.square
  (self : field.CM31) : Result field.CM31 := do
  let i := self.fst
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.snd
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← lift (Std.U64.wrapping_add i1 i3)
  let i5 ← lift (core.convert.num.FromU64U32.from i)
  let i6 ← lift (core.convert.num.FromU64U32.from field.P)
  let i7 ← lift (Std.U64.wrapping_add i5 i6)
  let i8 ← lift (core.convert.num.FromU64U32.from i2)
  let i9 ← lift (Std.U64.wrapping_sub i7 i8)
  let i10 ← lift (Std.U64.wrapping_mul i4 i9)
  let m ← field.M31.reduce_u64 i10
  let m1 ← field.M31.mul self.fst self.snd
  let m2 ← field.M31.double m1
  ok { fst := m, snd := m2 }

def field.CM31.double
  (self : field.CM31) : Result field.CM31 := do
  field.CM31.add self self

def field.CM31.inv_with
  (self : field.CM31)
  (inverse : field.M31 → Result field.M31) :
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

def field.CM31.inv
  (self : field.CM31) : Result field.CM31 := do
  field.CM31.inv_with self (field.M31.inv)

def field.mul_by_r
  (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.double x.fst
  let m1 ← field.M31.sub m x.snd
  let m2 ← field.M31.double x.snd
  let m3 ← field.M31.add x.fst m2
  ok { fst := m1, snd := m3 }

def field.QM31.ZERO : field.QM31 :=
  { fst := { fst := 0#u32, snd := 0#u32 }, snd := { fst := 0#u32, snd := 0#u32 } }

def field.QM31.ONE : field.QM31 :=
  { fst := { fst := 1#u32, snd := 0#u32 }, snd := { fst := 0#u32, snd := 0#u32 } }

def field.QM31.add
  (self : field.QM31) (rhs : field.QM31) :
  Result field.QM31
  := do
  let c ← field.CM31.add self.fst rhs.fst
  let c1 ← field.CM31.add self.snd rhs.snd
  ok { fst := c, snd := c1 }

def field.QM31.sub
  (self : field.QM31) (rhs : field.QM31) :
  Result field.QM31
  := do
  let c ← field.CM31.sub self.fst rhs.fst
  let c1 ← field.CM31.sub self.snd rhs.snd
  ok { fst := c, snd := c1 }

def field.QM31.mul
  (self : field.QM31) (rhs : field.QM31) :
  Result field.QM31
  := do
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

def field.QM31.square
  (self : field.QM31) : Result field.QM31 := do
  let c0_square ← field.CM31.square self.fst
  let c1_square ← field.CM31.square self.snd
  let c ← field.mul_by_r c1_square
  let c1 ← field.CM31.add c0_square c
  let c2 ← field.CM31.mul self.fst self.snd
  let c3 ← field.CM31.double c2
  ok { fst := c1, snd := c3 }

def field.CM31.is_zero
  (self : field.CM31) : Result Bool := do
  let b ← field.M31.is_zero self.fst
  let b1 ← field.M31.is_zero self.snd
  ok (b && b1)

def field.QM31.is_zero
  (self : field.QM31) : Result Bool := do
  let b ← field.CM31.is_zero self.fst
  let b1 ← field.CM31.is_zero self.snd
  ok (b && b1)

def field.QM31.try_inv
  (self : field.QM31) : Result (Option field.QM31) := do
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
#print axioms field.CM31.Insts.CoreCmpPartialEqCM31.eq
#print axioms field.CM31.ZERO
#print axioms field.CM31.ONE
#print axioms field.CM31.new
#print axioms field.CM31.add
#print axioms field.CM31.sub
#print axioms field.CM31.neg
#print axioms field.CM31.mul
#print axioms field.CM31.square
#print axioms field.CM31.double
#print axioms field.CM31.inv_with
#print axioms field.CM31.inv
#print axioms field.mul_by_r
#print axioms field.QM31.ZERO
#print axioms field.QM31.ONE
#print axioms field.QM31.add
#print axioms field.QM31.sub
#print axioms field.QM31.mul
#print axioms field.QM31.square
#print axioms field.CM31.is_zero
#print axioms field.QM31.is_zero
#print axioms field.QM31.try_inv
end R1Z.PV_RunJoin_CircleRawTower52
