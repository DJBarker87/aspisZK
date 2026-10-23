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
def mle50.count (width : Std.U8) : Result Std.U16 := do
  let i ← lift (core.convert.num.FromU32U8.from width)
  ok (core.num.U16.wrapping_shl 1#u16 i)

def mle50.mle
  (point : Array field.QM31 10#usize) (column : Array field.QM31 1024#usize) :
  Result field.QM31
  := do
  let width ← sparse_scan50.width point 10#u8
  let trailing ← lift (Std.U8.wrapping_sub 10#u8 width)
  let i ← lift (core.convert.num.FromUsizeU8.from width)
  let suffix ← sparse_scan50.suffix point i trailing
  let i1 ← mle50.count width
  sparse_sum50.sum point column width trailing suffix 0#usize i1
    field.QM31.ZERO

end AspisR1ProducerRelease47
