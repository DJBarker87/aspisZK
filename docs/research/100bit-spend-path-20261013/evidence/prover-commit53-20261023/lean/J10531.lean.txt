import AspisR1ProducerRelease47.MaskColumns51
import AspisR1ProducerRelease47.Points49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def claims53.go
  (point : Array field.QM31 10#usize)
  (columns : Array (Array field.QM31 1024#usize) 29#usize) (left : Std.U8)
  (out : Array field.QM31 29#usize) :
  Result (Array field.QM31 29#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let i ← lift (Std.U8.wrapping_sub 29#u8 left)
    let i1 ← lift (UScalar.cast .Usize i)
    let a ← Array.index_usize columns i1
    let q ← mle50.mle point a
    let out1 ← Array.update out i1 q
    let i2 ← lift (Std.U8.wrapping_sub left 1#u8)
    claims53.go point columns i2 out1
partial_fixpoint

def claims53.eval
  (point : Array field.QM31 10#usize)
  (columns : Array (Array field.QM31 1024#usize) 29#usize) :
  Result (Array field.QM31 29#usize)
  := do
  let a := Array.repeat 29#usize field.QM31.ZERO
  claims53.go point columns 29#u8 a

def claims53.all
  (alpha : Array field.QM31 10#usize)
  (columns : Array (Array field.QM31 1024#usize) 29#usize) :
  Result (Array (Array field.QM31 29#usize) 3#usize)
  := do
  let p ← points.all alpha
  let a ← Array.index_usize p 0#usize
  let a1 ← claims53.eval a columns
  let a2 ← Array.index_usize p 1#usize
  let a3 ← claims53.eval a2 columns
  let a4 ← Array.index_usize p 2#usize
  let a5 ← claims53.eval a4 columns
  ok (Array.make 3#usize [ a1, a3, a5 ])

end AspisR1ProducerRelease47
