import AspisR1ProducerRelease47.Factors49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def factors.line
  (x : field.QM31) (y : field.QM31) : Result (Array field.QM31 4#usize) := do
  let q ← field.QM31.mul x y
  ok (Array.make 4#usize [ field.QM31.ONE, x, y, q ])

def factors.lines
  (out : Array (Array field.QM31 4#usize) 5#usize) (d : Std.Usize)
  (left : Std.U8) (x : field.QM31) :
  Result (Array (Array field.QM31 4#usize) 5#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let y ← factors.double x
    let a ← factors.line x y
    let out1 ← Array.update out d a
    let next ← factors.double y
    let i ← lift (Std.Usize.wrapping_add d 1#usize)
    let i1 ← lift (Std.U8.wrapping_sub left 1#u8)
    factors.lines out1 i i1 next
partial_fixpoint

def factors.circle_rows
  (x : field.QM31) (y : field.QM31) :
  Result (Array (Array field.QM31 4#usize) 5#usize)
  := do
  let a := Array.repeat 4#usize field.QM31.ZERO
  let out := Array.repeat 5#usize a
  let a1 ← factors.circle x y
  let out1 ← Array.update out 0#usize a1
  let q ← factors.double x
  factors.lines out1 1#usize 4#u8 q

end AspisR1ProducerRelease47
