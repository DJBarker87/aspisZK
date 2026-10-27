import AspisR1ProducerRelease47.Basis
import AspisR1ProducerRelease47.Pairs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
@[global_simps, irreducible]
def field.M31.ZERO : field.M31 := 0#u32

def field.M31.ONE : field.M31 := 1#u32

def square_ref (x : field.M31) (left : Std.U8) : Result field.M31 := do
  if left = 0#u8
  then ok x
  else
    let m ← field.M31.mul x x
    let i ← lift (Std.U8.wrapping_sub left 1#u8)
    square_ref m i
partial_fixpoint

def inverse_ref (x : field.M31) : Result field.M31 := do
  massert (x != 0#u32)
  let m ← field.M31.mul x x
  let t2 ← field.M31.mul m x
  let m1 ← square_ref t2 2#u8
  let t4 ← field.M31.mul m1 t2
  let m2 ← square_ref t4 4#u8
  let t8 ← field.M31.mul m2 t4
  let m3 ← square_ref t8 8#u8
  let t16 ← field.M31.mul m3 t8
  let m4 ← square_ref t16 8#u8
  let t24 ← field.M31.mul m4 t8
  let m5 ← square_ref t24 4#u8
  let t28 ← field.M31.mul m5 t4
  let m6 ← field.M31.mul t28 t28
  let t29 ← field.M31.mul m6 x
  let t30 ← field.M31.mul t29 t29
  let m7 ← field.M31.mul t30 t30
  field.M31.mul m7 x

def scalar_ref (x : field.QM31) (y : field.M31) : Result field.QM31 := do
  let m ← field.M31.mul x.c0.a y
  let m1 ← field.M31.mul x.c0.b y
  let m2 ← field.M31.mul x.c1.a y
  let m3 ← field.M31.mul x.c1.b y
  ok { c0 := { a := m, b := m1 }, c1 := { a := m2, b := m3 } }

def predecessor
  (basis : Array field.M31 28#usize) (k : Std.Usize) : Result field.M31 := do
  if k = 0#usize
  then ok field.M31.ZERO
  else
    let i ← lift (Std.Usize.wrapping_sub k 1#usize)
    Array.index_usize basis i

def basis_mul
  (basis : Array field.M31 28#usize) (j : field.M31) (left : Std.U8) :
  Result (Array field.M31 28#usize)
  := do
  if left = 0#u8
  then ok basis
  else
    let i ← lift (Std.U8.wrapping_sub left 1#u8)
    let k ← lift (UScalar.cast .Usize i)
    let shifted ← predecessor basis k
    let m ← Array.index_usize basis k
    let m1 ← field.M31.mul m j
    let next ← field.M31.sub shifted m1
    let basis1 ← Array.update basis k next
    let i1 ← lift (Std.U8.wrapping_sub left 1#u8)
    basis_mul basis1 j i1
partial_fixpoint

def basis_factors
  (basis : Array field.M31 28#usize) (den : field.M31) (degree : Std.U8)
  (i : Std.U8) (j : Std.U8) (left : Std.U8) :
  Result ((Array field.M31 28#usize) × field.M31)
  := do
  if left = 0#u8
  then ok (basis, den)
  else
    if i = j
    then
      let i1 ← lift (Std.U8.wrapping_add j 1#u8)
      let i2 ← lift (Std.U8.wrapping_sub left 1#u8)
      basis_factors basis den degree i i1 i2
    else
      let i1 ← lift (UScalar.cast .U32 j)
      let i2 ← lift (Std.U8.wrapping_add degree 2#u8)
      let basis1 ← basis_mul basis i1 i2
      let i3 ← lift (UScalar.cast .U32 i)
      let i4 ← lift (UScalar.cast .U32 j)
      let m ← field.M31.sub i3 i4
      let den1 ← field.M31.mul den m
      let i5 ← lift (Std.U8.wrapping_add degree 1#u8)
      let i6 ← lift (Std.U8.wrapping_add j 1#u8)
      let i7 ← lift (Std.U8.wrapping_sub left 1#u8)
      basis_factors basis1 den1 i5 i i6 i7
partial_fixpoint

def accumulate
  (out : Array field.QM31 28#usize) (basis : Array field.M31 28#usize)
  (scale : field.QM31) (k : Std.U8) (left : Std.U8) :
  Result (Array field.QM31 28#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let index ← lift (UScalar.cast .Usize k)
    let q ← Array.index_usize out index
    let m ← Array.index_usize basis index
    let q1 ← scalar_ref scale m
    let next ← field.QM31.add q q1
    let out1 ← Array.update out index next
    let i ← lift (Std.U8.wrapping_add k 1#u8)
    let i1 ← lift (Std.U8.wrapping_sub left 1#u8)
    accumulate out1 basis scale i i1
partial_fixpoint

def rows
  (values : Array field.QM31 28#usize) (out : Array field.QM31 28#usize)
  (i : Std.U8) (left : Std.U8) :
  Result (Array field.QM31 28#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let basis := Array.repeat 28#usize field.M31.ZERO
    let basis1 ← Array.update basis 0#usize field.M31.ONE
    let (basis2, den) ← basis_factors basis1 field.M31.ONE 0#u8 i 0#u8 28#u8
    let i1 ← lift (UScalar.cast .Usize i)
    let q ← Array.index_usize values i1
    let m ← inverse_ref den
    let scale ← scalar_ref q m
    let out1 ← accumulate out basis2 scale 0#u8 28#u8
    let i2 ← lift (Std.U8.wrapping_add i 1#u8)
    let i3 ← lift (Std.U8.wrapping_sub left 1#u8)
    rows values out1 i2 i3
partial_fixpoint

def interpolate
  (values : Array field.QM31 28#usize) :
  Result (Array field.QM31 28#usize)
  := do
  let a := Array.repeat 28#usize field.QM31.ZERO
  rows values a 0#u8 28#u8

end AspisR1ProducerRelease47
