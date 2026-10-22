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
def mask_horner50.go
  (q : Array field.QM31 27#usize)
  (prepared : Array (Array field.M31 3#usize) 3#usize) (left : Std.U8)
  (acc : field.QM31) :
  Result field.QM31
  := do
  if left = 0#u8
  then ok acc
  else
    let n ← lift (Std.U8.wrapping_sub left 1#u8)
    let q1 ← prepared50.mul prepared acc
    let i ← lift (core.convert.num.FromUsizeU8.from n)
    let q2 ← Array.index_usize q i
    let value ← field.QM31.add q1 q2
    mask_horner50.go q prepared n value
partial_fixpoint

def mask_horner50.eval
  (q : Array field.QM31 27#usize) (x : field.QM31) : Result field.QM31 := do
  let prepared ← prepared50.prepare x
  let q1 ← Array.index_usize q 26#usize
  mask_horner50.go q prepared 26#u8 q1

end AspisR1ProducerRelease47
