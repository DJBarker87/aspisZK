import R1Z.ProverCommitInactiveSource49
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
def coefficients51.cell
  (rows : Array field.QM31 1024#usize) (j : Std.Usize) :
  Result field.QM31
  := do
  let i ← AspisR1InactiveOwner49.owned.row j
  Array.index_usize rows i

def coefficients51.go
  (rows : Array field.QM31 1024#usize) (left : Std.U16)
  (out : Array field.QM31 1024#usize) :
  Result (Array field.QM31 1024#usize)
  := do
  if left = 0#u16
  then ok out
  else
    let i ← lift (core.num.U16.wrapping_sub 1024#u16 left)
    let i1 ← lift (UScalar.cast .Usize i)
    let q ← coefficients51.cell rows i1
    let i2 ← lift (UScalar.cast .Usize i)
    let out1 ← Array.update out i2 q
    let i3 ← lift (core.num.U16.wrapping_sub left 1#u16)
    coefficients51.go rows i3 out1
partial_fixpoint

def coefficients51.eval
  (rows : Array field.QM31 1024#usize) :
  Result (Array field.QM31 1024#usize)
  := do
  let a := Array.repeat 1024#usize field.QM31.ZERO
  coefficients51.go rows 1024#u16 a

end AspisR1ProducerRelease47
