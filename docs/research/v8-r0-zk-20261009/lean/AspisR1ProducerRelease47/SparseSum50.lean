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
def sparse_sum50.sum
  (point : Array field.QM31 10#usize) (column : Array field.QM31 1024#usize)
  (width : Std.U8) (trailing : Std.U8) (suffix : Std.Usize) (pref : Std.Usize)
  (left : Std.U16) (acc : field.QM31) :
  Result field.QM31
  := do
  if left = 0#u16
  then ok acc
  else
    let weight ←
      sparse50.weight point pref width 0#usize width field.QM31.ONE
    let row ← sparse50.row pref trailing suffix
    let value ← Array.index_usize column row
    let product ← field.QM31.mul weight value
    let i ← lift (core.num.Usize.wrapping_add pref 1#usize)
    let i1 ← lift (Std.U16.wrapping_sub left 1#u16)
    let q ← field.QM31.add acc product
    sparse_sum50.sum point column width trailing suffix i i1 q
partial_fixpoint

end AspisR1ProducerRelease47
