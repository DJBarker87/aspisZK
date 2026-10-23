import AspisR1ProducerRelease47.Kernels49
import AspisR1ProducerRelease47.EncoderGeneric54
import AspisR1ProducerRelease47.Encoder54
import AspisR1ProducerRelease47.EncoderLeaf54
import AspisR1ProducerRelease47.EncoderNodes54
import AspisR1ProducerRelease47.Samples49
import AspisR1ProducerRelease47.Basis
import AspisR1ProducerRelease47.Opening48
import AspisR1ProducerRelease47.Pairs
/-! Extracted explicit recursive node builder, with identical arithmetic callees rebound to the
previously proved release extraction. bind-encoder-phi.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def nodes55.pow
  (base : field.CM31) (exp : Std.U64) (acc : field.CM31) :
  Result field.CM31
  := do
  if exp = 0#u64
  then ok acc
  else
    let i ← lift (exp &&& 1#u64)
    let next ← if i = 1#u64
                 then field.CM31.mul acc base
                 else ok acc
    let c ← field.CM31.square base
    let i1 ← lift (Std.U64.wrapping_shr exp 1#u32)
    nodes55.pow c i1 next
partial_fixpoint

end AspisR1ProducerRelease47
