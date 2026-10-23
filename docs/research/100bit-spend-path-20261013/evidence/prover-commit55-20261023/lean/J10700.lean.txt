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
def guarded55.eval_rec
  {T : Type} (scalarCodeFieldInst : scalar.CodeField T) (c : Slice T)
  (depth : Std.Usize) (height : Std.Usize) (nodes : Array field.M31 9#usize) :
  Result T
  := do
  let i := Slice.len c
  massert ((i = 1#usize) || (height > 0#usize))
  if i = 1#usize
  then Slice.index_usize c 0#usize
  else
    let i1 := Slice.len c
    let n ← i1 / 2#usize
    let even ←
      generic54.collect scalarCodeFieldInst c 2#usize 0#usize 0#usize n
        (alloc.vec.Vec.new T)
    let odd ←
      generic54.collect scalarCodeFieldInst c 2#usize 1#usize 0#usize n
        (alloc.vec.Vec.new T)
    let s := alloc.vec.Vec.deref even
    let i2 ← lift (Std.Usize.wrapping_add depth 1#usize)
    let i3 ← lift (Std.Usize.wrapping_sub height 1#usize)
    let a ← guarded55.eval_rec scalarCodeFieldInst s i2 i3 nodes
    let s1 := alloc.vec.Vec.deref odd
    let i4 ← lift (Std.Usize.wrapping_add depth 1#usize)
    let i5 ← lift (Std.Usize.wrapping_sub height 1#usize)
    let b ← guarded55.eval_rec scalarCodeFieldInst s1 i4 i5 nodes
    let m ← Array.index_usize nodes depth
    let t ← scalarCodeFieldInst.from_m31 m
    let t1 ← scalarCodeFieldInst.mul t b
    scalarCodeFieldInst.add a t1
partial_fixpoint

end AspisR1ProducerRelease47
