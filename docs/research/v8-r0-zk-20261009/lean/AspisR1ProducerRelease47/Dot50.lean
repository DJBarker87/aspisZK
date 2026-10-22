import AspisR1ProducerRelease47.Funs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def dot50.prepare_c (x : field.CM31) : Result (Array field.M31 3#usize) := do
  let m ← field.M31.add x.a x.b
  ok (Array.make 3#usize [ x.a, x.b, m ])

def dot50.prepare
  (x : field.QM31) : Result (Array (Array field.M31 3#usize) 3#usize) := do
  let z ← field.CM31.add x.c0 x.c1
  let a ← dot50.prepare_c x.c0
  let a1 ← dot50.prepare_c x.c1
  let a2 ← dot50.prepare_c z
  ok (Array.make 3#usize [ a, a1, a2 ])

end AspisR1ProducerRelease47
