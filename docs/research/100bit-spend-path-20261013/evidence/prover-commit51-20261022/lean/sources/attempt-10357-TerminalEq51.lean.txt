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
def terminal_eq51.factor
  (a : field.QM31) (b : field.QM31) : Result field.QM31 := do
  let ab ← field.QM31.mul a b
  let q ← field.QM31.sub field.QM31.ONE a
  let q1 ← field.QM31.sub q b
  let q2 ← field.QM31.add q1 ab
  field.QM31.add q2 ab

def terminal_eq51.go
  (left : Array field.QM31 10#usize) (right : Array field.QM31 10#usize)
  (index : Std.U8) (product : field.QM31) :
  Result field.QM31
  := do
  if index = 10#u8
  then ok product
  else
    let i ← lift (UScalar.cast .Usize index)
    let q ← Array.index_usize left i
    let i1 ← lift (UScalar.cast .Usize index)
    let q1 ← Array.index_usize right i1
    let q2 ← terminal_eq51.factor q q1
    let next ← field.QM31.mul product q2
    let i2 ← lift (core.num.U8.wrapping_add index 1#u8)
    terminal_eq51.go left right i2 next
partial_fixpoint

def terminal_eq51.eval
  (left : Array field.QM31 10#usize) (right : Array field.QM31 10#usize) :
  Result field.QM31
  := do
  let q ← Array.index_usize left 0#usize
  let q1 ← Array.index_usize right 0#usize
  let product ← terminal_eq51.factor q q1
  terminal_eq51.go left right 1#u8 product

def terminal_eq51.suffix
  (eq : field.QM31) (composition : field.QM31) (h1 : field.QM31)
  (active : field.QM31) (mu : field.QM31) :
  Result field.QM31
  := do
  let q ← field.QM31.mul eq composition
  let q1 ← field.QM31.mul mu h1
  let q2 ← field.QM31.add q q1
  let q3 ← field.QM31.mul mu mu
  let q4 ← field.QM31.sub field.QM31.ONE active
  let q5 ← field.QM31.mul q4 h1
  let q6 ← field.QM31.mul q3 q5
  field.QM31.add q2 q6

end AspisR1ProducerRelease47
