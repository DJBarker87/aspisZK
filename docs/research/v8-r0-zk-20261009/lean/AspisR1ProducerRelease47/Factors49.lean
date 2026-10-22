import AspisR1ProducerRelease47.Basis
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def factors.point
  (a : field.QM31) (b : field.QM31) : Result (Array field.QM31 4#usize) := do
  let q ← field.QM31.sub field.QM31.ONE a
  let q1 ← field.QM31.sub field.QM31.ONE b
  let q2 ← field.QM31.mul q q1
  let q3 ← field.QM31.mul a q1
  let q4 ← field.QM31.mul q b
  let q5 ← field.QM31.mul a b
  ok (Array.make 4#usize [ q2, q3, q4, q5 ])

def factors.circle
  (x : field.QM31) (y : field.QM31) : Result (Array field.QM31 4#usize) := do
  let q ← field.QM31.mul x y
  ok (Array.make 4#usize [ field.QM31.ONE, y, x, q ])

def factors.double (x : field.QM31) : Result field.QM31 := do
  let q ← field.QM31.mul x x
  let q1 ← field.QM31.add q q
  field.QM31.sub q1 field.QM31.ONE

def factors.product
  (q : Array field.QM31 5#usize) (i : Std.Usize) (left : Std.U8)
  (s : field.QM31) :
  Result field.QM31
  := do
  if left = 0#u8
  then ok s
  else
    let q1 ← Array.index_usize q i
    let next ← field.QM31.mul s q1
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    let i2 ← lift (Std.U8.wrapping_sub left 1#u8)
    factors.product q i1 i2 next
partial_fixpoint

end AspisR1ProducerRelease47
