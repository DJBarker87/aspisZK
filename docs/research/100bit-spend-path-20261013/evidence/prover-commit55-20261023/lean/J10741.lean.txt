import AspisR1ProducerRelease47.EncoderGuard55
import AspisR1ProducerRelease47.EncoderNativeGeometry55
import AspisR1ProducerRelease47.EncoderNativeNodes55
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
def guarded55.channels
  {T : Type} (scalarCodeFieldInst : scalar.CodeField T)
  (c : Array T 1024#usize) (nodes : Array field.M31 9#usize) :
  Result (Array T 4#usize)
  := do
  let s ← lift (Array.to_slice c)
  let a ←
    generic54.collect scalarCodeFieldInst s 4#usize 0#usize 0#usize 256#usize
      (alloc.vec.Vec.new T)
  let s1 ← lift (Array.to_slice c)
  let b ←
    generic54.collect scalarCodeFieldInst s1 4#usize 1#usize 0#usize 256#usize
      (alloc.vec.Vec.new T)
  let s2 ← lift (Array.to_slice c)
  let d ←
    generic54.collect scalarCodeFieldInst s2 4#usize 2#usize 0#usize 256#usize
      (alloc.vec.Vec.new T)
  let s3 ← lift (Array.to_slice c)
  let e ←
    generic54.collect scalarCodeFieldInst s3 4#usize 3#usize 0#usize 256#usize
      (alloc.vec.Vec.new T)
  let s4 := alloc.vec.Vec.deref a
  let t ← guarded55.eval_rec scalarCodeFieldInst s4 0#usize 8#usize nodes
  let s5 := alloc.vec.Vec.deref b
  let t1 ← guarded55.eval_rec scalarCodeFieldInst s5 0#usize 8#usize nodes
  let s6 := alloc.vec.Vec.deref d
  let t2 ← guarded55.eval_rec scalarCodeFieldInst s6 0#usize 8#usize nodes
  let s7 := alloc.vec.Vec.deref e
  let t3 ← guarded55.eval_rec scalarCodeFieldInst s7 0#usize 8#usize nodes
  ok (Array.make 4#usize [ t, t1, t2, t3 ])

def guarded55.eval_at
  {T : Type} (scalarCodeFieldInst : scalar.CodeField T) (c : Slice T)
  (j : Std.Usize) (height : Std.Usize) :
  Result T
  := do
  let nodes ← nodes55.nodes j
  guarded55.eval_rec scalarCodeFieldInst c 0#usize height nodes

def guarded55.encode_at
  {T : Type} (scalarCodeFieldInst : scalar.CodeField T)
  (c : Array T 1024#usize) (j : Std.Usize) :
  Result (Array T 4#usize)
  := do
  let z ← nodes55.point j
  let nodes ← nodes55.nodes j
  let h ← guarded55.channels scalarCodeFieldInst c nodes
  let t ← scalarCodeFieldInst.from_m31 z.a
  let t1 ← scalarCodeFieldInst.from_m31 z.b
  generic54.phi_inverse scalarCodeFieldInst t t1 h

end AspisR1ProducerRelease47
