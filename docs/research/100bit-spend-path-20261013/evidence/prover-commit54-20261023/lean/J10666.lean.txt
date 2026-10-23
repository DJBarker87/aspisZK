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
def generic54.eval_at
  {E : Type} (scalarCodeFieldInst : scalar.CodeField E) (c : Slice E)
  (j : Std.Usize) (height : Std.Usize) :
  Result E
  := do
  let nodes ← nodes54.nodes j
  generic54.eval_rec scalarCodeFieldInst c 0#usize height nodes

def generic54.encode_at
  {E : Type} (scalarCodeFieldInst : scalar.CodeField E)
  (c : Array E 1024#usize) (j : Std.Usize) :
  Result (Array E 4#usize)
  := do
  let z ← nodes54.point j
  let nodes ← nodes54.nodes j
  let t ← scalarCodeFieldInst.from_m31 z.a
  let t1 ← scalarCodeFieldInst.from_m31 z.b
  generic54.encode_with_nodes scalarCodeFieldInst c nodes t t1

end AspisR1ProducerRelease47
