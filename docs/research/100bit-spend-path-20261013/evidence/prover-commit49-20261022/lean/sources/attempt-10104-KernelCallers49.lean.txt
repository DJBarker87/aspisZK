import AspisR1ProducerRelease47.Kernels49
import AspisR1ProducerRelease47.Samples49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def extras.half : Result field.QM31 := do
  let m ← inverse_ref 2#u32
  let c ← field.CM31.from_m31 m
  field.QM31.from_cm31 c

def extras.libra
  (extra : Array field.QM31 2#usize) (j : Std.Usize) : Result field.QM31 := do
  if j < 56#usize
  then
    let i ← j / 28#usize
    let q ← Array.index_usize extra i
    let i1 ← j % 28#usize
    let i2 ← lift (UScalar.cast .U8 i1)
    kernels.power q i2 field.QM31.ONE
  else ok field.QM31.ZERO

end AspisR1ProducerRelease47
