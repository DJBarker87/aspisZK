import AspisR1ProducerRelease47.Interpolate48
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def field.M31.neg (self : field.M31) : Result field.M31 := do
  if self = 0#u32
  then ok 0#u32
  else let i ← lift (Std.U32.wrapping_sub field.P self)
       ok i

def field.M31.is_zero (self : field.M31) : Result Bool := do
  ok (self = 0#u32)

def field.CM31.neg (self : field.CM31) : Result field.CM31 := do
  let m ← field.M31.neg self.a
  let m1 ← field.M31.neg self.b
  ok { a := m, b := m1 }

def field.CM31.square (self : field.CM31) : Result field.CM31 := do
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← lift (Std.U64.wrapping_add i1 i3)
  let i5 ← lift (core.convert.num.FromU64U32.from i)
  let i6 ← lift (core.convert.num.FromU64U32.from field.P)
  let i7 ← lift (Std.U64.wrapping_add i5 i6)
  let i8 ← lift (core.convert.num.FromU64U32.from i2)
  let i9 ← lift (Std.U64.wrapping_sub i7 i8)
  let i10 ← lift (Std.U64.wrapping_mul i4 i9)
  let m ← field.M31.reduce_u64 i10
  let m1 ← field.M31.mul self.a self.b
  let m2 ← field.M31.double m1
  ok { a := m, b := m2 }

def field.CM31.double (self : field.CM31) : Result field.CM31 := do
  field.CM31.add self self

def field.CM31.is_zero (self : field.CM31) : Result Bool := do
  let b ← field.M31.is_zero self.a
  if b
  then field.M31.is_zero self.b
  else ok false

def field.QM31.square (self : field.QM31) : Result field.QM31 := do
  let c0_square ← field.CM31.square self.c0
  let c1_square ← field.CM31.square self.c1
  let c ← field.mul_by_r c1_square
  let c1 ← field.CM31.add c0_square c
  let c2 ← field.CM31.mul self.c0 self.c1
  let c3 ← field.CM31.double c2
  ok { c0 := c1, c1 := c3 }

def field.QM31.is_zero (self : field.QM31) : Result Bool := do
  let b ← field.CM31.is_zero self.c0
  if b
  then field.CM31.is_zero self.c1
  else ok false

def kernels.square (x : field.QM31) : Result field.QM31 := do
  field.QM31.square x

def kernels.power
  (base : field.QM31) (exp : Std.U8) (acc : field.QM31) :
  Result field.QM31
  := do
  if exp = 0#u8
  then ok acc
  else
    let i ← lift (exp &&& 1#u8)
    let next ← if i != 0#u8
                 then field.QM31.mul acc base
                 else ok acc
    let q ← field.QM31.square base
    let i1 ← lift (Std.U8.wrapping_shr exp 1#u32)
    kernels.power q i1 next
partial_fixpoint

def kernels.inverse_c (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.mul x.a x.a
  let m1 ← field.M31.mul x.b x.b
  let norm ← field.M31.add m m1
  let inv_norm ← inverse_ref norm
  let m2 ← field.M31.mul x.a inv_norm
  let m3 ← field.M31.neg x.b
  let m4 ← field.M31.mul m3 inv_norm
  ok { a := m2, b := m4 }

def kernels.mul_r (x : field.CM31) : Result field.CM31 := do
  let two_a ← field.M31.double x.a
  let real ← field.M31.sub two_a x.b
  let two_b ← field.M31.double x.b
  let imag ← field.M31.add x.a two_b
  ok { a := real, b := imag }

def kernels.inverse_q (x : field.QM31) : Result (Option field.QM31) := do
  let b ← field.QM31.is_zero x
  if b
  then ok none
  else
    let c ← field.CM31.square x.c0
    let c1 ← field.CM31.square x.c1
    let c2 ← kernels.mul_r c1
    let norm ← field.CM31.sub c c2
    let ni ← kernels.inverse_c norm
    let c3 ← field.CM31.mul x.c0 ni
    let c4 ← field.CM31.neg x.c1
    let c5 ← field.CM31.mul c4 ni
    ok (some { c0 := c3, c1 := c5 })

end AspisR1ProducerRelease47
