import AspisR1ProducerRelease47.Interpolate48
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
@[global_simps, irreducible]
def field.CM31.ZERO : field.CM31 := { a := 0#u32, b := 0#u32 }

def field.CM31.from_m31 (a : field.M31) : Result field.CM31 := do
  ok { a, b := field.M31.ZERO }

def field.QM31.from_cm31 (c0 : field.CM31) : Result field.QM31 := do
  ok { c0, c1 := field.CM31.ZERO }

def owned.sum
  (values : Array field.QM31 512#usize) (start : Std.Usize) (left : Std.U16)
  (total : field.QM31) :
  Result field.QM31
  := do
  if left = 0#u16
  then ok total
  else
    let q ← Array.index_usize values start
    let next ← field.QM31.add total q
    let i ← lift (Std.Usize.wrapping_add start 1#usize)
    let i1 ← lift (Std.U16.wrapping_sub left 1#u16)
    owned.sum values i i1 next
partial_fixpoint

def owned.tail
  (point : Array field.QM31 10#usize) (round : Std.Usize)
  (remaining : Std.Usize) (assignment : Std.Usize) (offset : Std.Usize)
  (left : Std.U8) :
  Result (Array field.QM31 10#usize)
  := do
  if left = 0#u8
  then ok point
  else
    let i ← lift (Std.Usize.wrapping_sub remaining 1#usize)
    let i1 ← lift (Std.Usize.wrapping_sub i offset)
    let i2 ← lift (UScalar.cast .U32 i1)
    let i3 ← lift (Std.Usize.wrapping_shr assignment i2)
    let i4 ← lift (i3 &&& 1#usize)
    let q ← if i4 = 0#usize
              then ok field.QM31.ZERO
              else ok field.QM31.ONE
    let i5 ← lift (Std.Usize.wrapping_add round 1#usize)
    let i6 ← lift (Std.Usize.wrapping_add i5 offset)
    let point1 ← Array.update point i6 q
    let i7 ← lift (Std.Usize.wrapping_add offset 1#usize)
    let i8 ← lift (Std.U8.wrapping_sub left 1#u8)
    owned.tail point1 round remaining assignment i7 i8
partial_fixpoint

def owned.sample
  (point : Array field.QM31 10#usize) (round : Std.Usize) (sample : Std.U32) :
  Result (Array field.QM31 10#usize)
  := do
  let c ← field.CM31.from_m31 sample
  let q ← field.QM31.from_cm31 c
  Array.update point round q

def owned.shift
  (p : Array field.QM31 28#usize) (original : field.QM31)
  (eta_term0 : field.QM31) (inv : field.QM31) (half : field.QM31) :
  Result (Array field.QM31 28#usize)
  := do
  let q ← field.QM31.sub original eta_term0
  let c ← field.QM31.mul q inv
  let q1 ← Array.index_usize p 0#usize
  let q2 ← field.QM31.mul c half
  let q3 ← field.QM31.sub q1 q2
  let p1 ← Array.update p 0#usize q3
  let q4 ← Array.index_usize p1 1#usize
  let q5 ← field.QM31.add q4 c
  Array.update p1 1#usize q5

end AspisR1ProducerRelease47
