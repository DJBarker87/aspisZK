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
def linear50.go
  (point : Array field.QM31 10#usize) (left : Std.U8) (suffix : field.QM31)
  (weighted : field.QM31) :
  Result (field.QM31 × field.QM31)
  := do
  if left = 0#u8
  then ok (suffix, weighted)
  else
    let n ← lift (Std.U8.wrapping_sub left 1#u8)
    let i ← lift (core.convert.num.FromUsizeU8.from n)
    let q ← Array.index_usize point i
    let next ← field.QM31.add suffix q
    let weighted1 ←
      if n = 0#u8
      then ok weighted
      else field.QM31.add weighted next
    linear50.go point n next weighted1
partial_fixpoint

def linear50.eval
  (point : Array field.QM31 10#usize) : Result (field.QM31 × field.QM31) := do
  let (suffix, weighted) ←
    linear50.go point 10#u8 field.QM31.ZERO field.QM31.ZERO
  let q ← field.QM31.mul_m31 suffix 3#u32
  let q1 ← field.QM31.mul_m31 weighted 22#u32
  let q2 ← field.QM31.add q q1
  let q3 ← field.QM31.mul_m31 suffix 275#u32
  let q4 ← field.QM31.mul_m31 weighted 150#u32
  let q5 ← field.QM31.add q3 q4
  ok (q2, q5)

def linear50.power26 (x : field.QM31) : Result field.QM31 := do
  let x2 ← field.QM31.square x
  let x4 ← field.QM31.square x2
  let x8 ← field.QM31.square x4
  let x16 ← field.QM31.square x8
  let q ← field.QM31.mul x16 x8
  field.QM31.mul q x2

end AspisR1ProducerRelease47
