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
def eval_at
  (c : Slice field.wide_exact.WideExact) (j : Std.Usize) (height : Std.Usize) :
  Result field.wide_exact.WideExact
  := do
  let nodes ← nodes54.nodes j
  encoder54.eval_rec c 0#usize height nodes

def encode_at
  (c : Array field.wide_exact.WideExact 1024#usize) (j : Std.Usize) :
  Result (Array field.wide_exact.WideExact 4#usize)
  := do
  let z ← nodes54.point j
  let nodes ← nodes54.nodes j
  let c1 ← field.CM31.from_m31 z.a
  let q ← field.QM31.from_cm31 c1
  let x ← field.wide_exact.WideExact.from_qm31 q
  let c2 ← field.CM31.from_m31 z.b
  let q1 ← field.QM31.from_cm31 c2
  let y ← field.wide_exact.WideExact.from_qm31 q1
  encoder54.encode_with_nodes c nodes x y

end AspisR1ProducerRelease47
