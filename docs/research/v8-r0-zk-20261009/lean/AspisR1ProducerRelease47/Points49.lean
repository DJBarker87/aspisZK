import AspisR1ProducerRelease47.Basis
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def points.successor
  (p : Array field.QM31 10#usize) (out : Array field.QM31 10#usize)
  (left : Std.U8) (carry : field.QM31) :
  Result (Array field.QM31 10#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let i ← lift (Std.U8.wrapping_sub left 1#u8)
    let coordinate ← lift (UScalar.cast .Usize i)
    let bit ← Array.index_usize p coordinate
    let bc ← field.QM31.mul bit carry
    let q ← field.QM31.add bit carry
    let q1 ← field.QM31.add bc bc
    let q2 ← field.QM31.sub q q1
    let out1 ← Array.update out coordinate q2
    let i1 ← lift (Std.U8.wrapping_sub left 1#u8)
    points.successor p out1 i1 bc
partial_fixpoint

def points.absorption
  (p : Array field.QM31 10#usize) : Result (Array field.QM31 10#usize) := do
  let q ← Array.index_usize p 7#usize
  let q1 ← field.QM31.sub field.QM31.ONE q
  let p1 ← Array.update p 7#usize q1
  let q2 ← Array.index_usize p1 6#usize
  let q3 ← field.QM31.sub field.QM31.ONE q2
  Array.update p1 6#usize q3

def points.all
  (p : Array field.QM31 10#usize) :
  Result (Array (Array field.QM31 10#usize) 3#usize)
  := do
  let a ← points.successor p p 10#u8 field.QM31.ONE
  let a1 ← points.absorption p
  ok (Array.make 3#usize [ p, a, a1 ])

end AspisR1ProducerRelease47
