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
def eval50.block
  (p : Array field.QM31 28#usize) (powers : Array field.QM31 3#usize)
  (j : Std.Usize) :
  Result field.QM31
  := do
  let start ← lift (core.num.Usize.wrapping_mul j 4#usize)
  let q ← Array.index_usize p start
  let i ← lift (core.num.Usize.wrapping_add start 1#usize)
  let q1 ← Array.index_usize p i
  let i1 ← lift (core.num.Usize.wrapping_add start 2#usize)
  let q2 ← Array.index_usize p i1
  let i2 ← lift (core.num.Usize.wrapping_add start 3#usize)
  let q3 ← Array.index_usize p i2
  let q4 ← run50.run powers (Array.make 3#usize [ q1, q2, q3 ])
  field.QM31.add q q4

def eval50.go
  (p : Array field.QM31 28#usize) (powers : Array field.QM31 3#usize)
  (prepared : Array (Array field.M31 3#usize) 3#usize) (left : Std.U8)
  (acc : field.QM31) :
  Result field.QM31
  := do
  if left = 0#u8
  then ok acc
  else
    let n ← lift (Std.U8.wrapping_sub left 1#u8)
    let product ← prepared50.mul prepared acc
    let i ← lift (core.convert.num.FromUsizeU8.from n)
    let value ← eval50.block p powers i
    let q ← field.QM31.add product value
    eval50.go p powers prepared n q
partial_fixpoint

def eval50.eval
  (p : Array field.QM31 28#usize) (x : field.QM31) : Result field.QM31 := do
  let x2 ← field.QM31.square x
  let x3 ← field.QM31.mul x x2
  let x4 ← field.QM31.square x2
  let prepared ← prepared50.prepare x4
  let acc ← eval50.block p (Array.make 3#usize [ x, x2, x3 ]) 6#usize
  eval50.go p (Array.make 3#usize [ x, x2, x3 ]) prepared 6#u8 acc

end AspisR1ProducerRelease47
