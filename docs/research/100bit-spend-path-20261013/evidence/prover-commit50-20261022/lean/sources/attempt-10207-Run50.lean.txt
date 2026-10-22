import AspisR1ProducerRelease47.Dot50
import AspisR1ProducerRelease47.Totals50
import AspisR1ProducerRelease47.Reconstruction49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def run50.prepare3
  (x : Array field.QM31 3#usize) :
  Result (Array (Array (Array field.M31 3#usize) 3#usize) 3#usize)
  := do
  let q ← Array.index_usize x 0#usize
  let a ← dot50.prepare q
  let q1 ← Array.index_usize x 1#usize
  let a1 ← dot50.prepare q1
  let q2 ← Array.index_usize x 2#usize
  let a2 ← dot50.prepare q2
  ok (Array.make 3#usize [ a, a1, a2 ])

def run50.run
  (x : Array field.QM31 3#usize) (y : Array field.QM31 3#usize) :
  Result field.QM31
  := do
  let a ← run50.prepare3 x
  let b ← run50.prepare3 y
  let a1 ← totals50.all a b
  reconstruction.q a1

end AspisR1ProducerRelease47
