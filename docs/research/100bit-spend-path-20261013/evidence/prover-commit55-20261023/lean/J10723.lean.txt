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
def nodes55.point (j : Std.Usize) : Result field.CM31 := do
  let r ← nodes54.reverse 18#u8 j
  let c ← field.CM31.new 2#u32 1268011823#u32
  let i ← lift (UScalar.cast .U64 r)
  let i1 ← lift (Std.U64.wrapping_mul 4096#u64 i)
  let i2 ← lift (Std.U64.wrapping_add 1024#u64 i1)
  nodes55.pow c i2 field.CM31.ONE

def nodes55.node (j : Std.Usize) (depth : Std.U8) : Result field.M31 := do
  let i ← lift (UScalar.cast .U32 depth)
  let step ← lift (Std.Usize.wrapping_shl 1#usize i)
  let i1 ← j / step
  let aligned ← lift (Std.Usize.wrapping_mul i1 step)
  let c ← nodes55.point aligned
  let i2 ← lift (Std.U8.wrapping_add depth 1#u8)
  nodes54.repeat c.a i2

def nodes55.fill
  (j : Std.Usize) (d : Std.U8) (left : Std.U8) (out : Array field.M31 9#usize)
  :
  Result (Array field.M31 9#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let m ← nodes55.node j d
    let i ← lift (UScalar.cast .Usize d)
    let out1 ← Array.update out i m
    let i1 ← lift (Std.U8.wrapping_add d 1#u8)
    let i2 ← lift (Std.U8.wrapping_sub left 1#u8)
    nodes55.fill j i1 i2 out1
partial_fixpoint

def nodes55.nodes (j : Std.Usize) : Result (Array field.M31 9#usize) := do
  let a := Array.repeat 9#usize field.M31.ZERO
  nodes55.fill j 0#u8 9#u8 a

end AspisR1ProducerRelease47
