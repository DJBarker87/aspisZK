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
def mask_coeff51.go
  (input : Array field.QM31 26#usize) (exponents : Array Std.U8 26#usize)
  (left : Std.U8) (out : Array field.QM31 27#usize) :
  Result (Array field.QM31 27#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let i ← lift (core.num.U8.wrapping_sub 26#u8 left)
    let i1 ← lift (UScalar.cast .Usize i)
    let q ← Array.index_usize input i1
    let i2 ← i % 4#u8
    let v ← tower50.mul q i2
    let i3 ← lift (UScalar.cast .Usize i)
    let i4 ← Array.index_usize exponents i3
    let i5 ← lift (UScalar.cast .Usize i4)
    let out1 ← Array.update out i5 v
    let i6 ← lift (core.num.U8.wrapping_sub left 1#u8)
    mask_coeff51.go input exponents i6 out1
partial_fixpoint

def mask_coeff51.eval
  (input : Array field.QM31 26#usize) (exponents : Array Std.U8 26#usize) :
  Result (Array field.QM31 27#usize)
  := do
  let a := Array.repeat 27#usize field.QM31.ZERO
  mask_coeff51.go input exponents 26#u8 a

end AspisR1ProducerRelease47
