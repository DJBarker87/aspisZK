import AspisR1ProducerRelease47.Linear50
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
def mask_finish50.eval
  (shared : field.QM31) (explicit_linear : field.QM31) (g : field.QM31) :
  Result field.QM31
  := do
  let q ← linear50.power26 explicit_linear
  let q1 ← field.QM31.add field.QM31.ONE q
  let q2 ← field.QM31.mul q1 g
  field.QM31.add shared q2

end AspisR1ProducerRelease47
