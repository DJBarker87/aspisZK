import AspisR1ProducerRelease47.Mle50
import AspisR1ProducerRelease47.Tower50
import AspisR1ProducerRelease47.Batched48
import AspisR1ProducerRelease47.SparseScan50
import AspisR1ProducerRelease47.SparseSum50
import AspisR1ProducerRelease47.Sparse50
import AspisR1ProducerRelease47.Kernels49
import AspisR1ProducerRelease47.Prepared50
import AspisR1ProducerRelease47.Run50
import AspisR1ProducerRelease47.Dot50
import AspisR1ProducerRelease47.Totals50
import AspisR1ProducerRelease47.Reconstruction49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def mask_columns51.go
  (point : Array field.QM31 10#usize)
  (columns : Array (Array field.QM31 1024#usize) 26#usize) (left : Std.U8)
  (out : Array field.QM31 26#usize) :
  Result (Array field.QM31 26#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let i ← lift (core.num.U8.wrapping_sub 26#u8 left)
    let i1 ← lift (UScalar.cast .Usize i)
    let a ← Array.index_usize columns i1
    let q ← mle50.mle point a
    let i2 ← lift (UScalar.cast .Usize i)
    let out1 ← Array.update out i2 q
    let i3 ← lift (core.num.U8.wrapping_sub left 1#u8)
    mask_columns51.go point columns i3 out1
partial_fixpoint

def mask_columns51.eval
  (point : Array field.QM31 10#usize)
  (columns : Array (Array field.QM31 1024#usize) 26#usize) :
  Result (Array field.QM31 26#usize)
  := do
  let a := Array.repeat 26#usize field.QM31.ZERO
  mask_columns51.go point columns 26#u8 a

end AspisR1ProducerRelease47
