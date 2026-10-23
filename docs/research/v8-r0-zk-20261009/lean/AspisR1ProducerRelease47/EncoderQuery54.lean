import AspisR1ProducerRelease47.EncoderLeaves54
import AspisR1ProducerRelease47.EncoderComplete54
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
def leaves54.folded_query
  (c : Array field.wide_exact.WideExact 256#usize) (q : Std.U32) :
  Result (Array field.wide_exact.WideExact 4#usize)
  := do
  let i ← lift (UScalar.cast .Usize q)
  let i1 ← i / 4#usize
  leaves54.folded_values c i1

def leaves54.opened_query
  (c : Array (Array field.wide_exact.WideExact 1024#usize) 29#usize)
  (q : Std.U32) :
  Result (Array (Array field.wide_exact.WideExact 29#usize) 4#usize)
  := do
  let i ← lift (UScalar.cast .Usize q)
  leaves54.opened_values c i

end AspisR1ProducerRelease47
