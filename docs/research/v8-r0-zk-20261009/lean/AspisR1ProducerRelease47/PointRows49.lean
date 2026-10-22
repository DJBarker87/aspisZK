import AspisR1ProducerRelease47.CircleFactors49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def point_rows.TAU : Array Std.Usize 5#usize :=
  Array.make 5#usize [ 3#usize, 4#usize, 2#usize, 0#usize, 1#usize ]

def point_rows.fill
  (p : Array field.QM31 10#usize)
  (out : Array (Array field.QM31 4#usize) 5#usize) (d : Std.Usize)
  (left : Std.U8) :
  Result (Array (Array field.QM31 4#usize) 5#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let t ← Array.index_usize point_rows.TAU d
    let i ← lift (Std.Usize.wrapping_mul 2#usize t)
    let i1 ← lift (Std.Usize.wrapping_sub 9#usize i)
    let a ← Array.index_usize p i1
    let i2 ← lift (Std.Usize.wrapping_mul 2#usize t)
    let i3 ← lift (Std.Usize.wrapping_sub 8#usize i2)
    let b ← Array.index_usize p i3
    let a1 ← factors.point a b
    let out1 ← Array.update out d a1
    let i4 ← lift (Std.Usize.wrapping_add d 1#usize)
    let i5 ← lift (Std.U8.wrapping_sub left 1#u8)
    point_rows.fill p out1 i4 i5
partial_fixpoint

def point_rows.all
  (p : Array field.QM31 10#usize) :
  Result (Array (Array field.QM31 4#usize) 5#usize)
  := do
  let a := Array.repeat 4#usize field.QM31.ZERO
  let a1 := Array.repeat 5#usize a
  point_rows.fill p a1 0#usize 5#u8

end AspisR1ProducerRelease47
