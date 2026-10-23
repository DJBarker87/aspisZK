import AspisR1ProducerRelease47.Samples49
import AspisR1ProducerRelease47.Basis
import AspisR1ProducerRelease47.Opening48
import AspisR1ProducerRelease47.Pairs
/-! Extracted explicit recursive encoder, with identical arithmetic callees rebound to the
previously proved release extraction. bind-encoder-phi.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def encoder54.collect
  (c : Slice field.wide_exact.WideExact) (stride : Std.Usize)
  (offset : Std.Usize) (i : Std.Usize) (left : Std.Usize)
  (out : alloc.vec.Vec field.wide_exact.WideExact) :
  Result (alloc.vec.Vec field.wide_exact.WideExact)
  := do
  if left = 0#usize
  then ok out
  else
    let i1 ← lift (Std.Usize.wrapping_mul stride i)
    let i2 ← lift (Std.Usize.wrapping_add i1 offset)
    let we ← Slice.index_usize c i2
    let out1 ← alloc.vec.Vec.push out we
    let i3 ← lift (Std.Usize.wrapping_add i 1#usize)
    let i4 ← lift (Std.Usize.wrapping_sub left 1#usize)
    encoder54.collect c stride offset i3 i4 out1
partial_fixpoint

def encoder54.eval_rec
  (c : Slice field.wide_exact.WideExact) (depth : Std.Usize)
  (height : Std.Usize) (nodes : Array field.M31 9#usize) :
  Result field.wide_exact.WideExact
  := do
  if height = 0#usize
  then Slice.index_usize c 0#usize
  else
    let i := Slice.len c
    let n ← i / 2#usize
    let even ←
      encoder54.collect c 2#usize 0#usize 0#usize n (alloc.vec.Vec.new
        field.wide_exact.WideExact)
    let odd ←
      encoder54.collect c 2#usize 1#usize 0#usize n (alloc.vec.Vec.new
        field.wide_exact.WideExact)
    let s := alloc.vec.Vec.deref even
    let i1 ← lift (Std.Usize.wrapping_add depth 1#usize)
    let i2 ← lift (Std.Usize.wrapping_sub height 1#usize)
    let a ← encoder54.eval_rec s i1 i2 nodes
    let s1 := alloc.vec.Vec.deref odd
    let i3 ← lift (Std.Usize.wrapping_add depth 1#usize)
    let i4 ← lift (Std.Usize.wrapping_sub height 1#usize)
    let b ← encoder54.eval_rec s1 i3 i4 nodes
    let m ← Array.index_usize nodes depth
    let c1 ← field.CM31.from_m31 m
    let q ← field.QM31.from_cm31 c1
    let we ← field.wide_exact.WideExact.from_qm31 q
    let we1 ← field.wide_exact.WideExact.mul we b
    field.wide_exact.WideExact.add a we1
partial_fixpoint

def encoder54.channels
  (c : Array field.wide_exact.WideExact 1024#usize)
  (nodes : Array field.M31 9#usize) :
  Result (Array field.wide_exact.WideExact 4#usize)
  := do
  let s ← lift (Array.to_slice c)
  let a ←
    encoder54.collect s 4#usize 0#usize 0#usize 256#usize (alloc.vec.Vec.new
      field.wide_exact.WideExact)
  let s1 ← lift (Array.to_slice c)
  let b ←
    encoder54.collect s1 4#usize 1#usize 0#usize 256#usize (alloc.vec.Vec.new
      field.wide_exact.WideExact)
  let s2 ← lift (Array.to_slice c)
  let d ←
    encoder54.collect s2 4#usize 2#usize 0#usize 256#usize (alloc.vec.Vec.new
      field.wide_exact.WideExact)
  let s3 ← lift (Array.to_slice c)
  let e ←
    encoder54.collect s3 4#usize 3#usize 0#usize 256#usize (alloc.vec.Vec.new
      field.wide_exact.WideExact)
  let s4 := alloc.vec.Vec.deref a
  let we ← encoder54.eval_rec s4 0#usize 8#usize nodes
  let s5 := alloc.vec.Vec.deref b
  let we1 ← encoder54.eval_rec s5 0#usize 8#usize nodes
  let s6 := alloc.vec.Vec.deref d
  let we2 ← encoder54.eval_rec s6 0#usize 8#usize nodes
  let s7 := alloc.vec.Vec.deref e
  let we3 ← encoder54.eval_rec s7 0#usize 8#usize nodes
  ok (Array.make 4#usize [ we, we1, we2, we3 ])

end AspisR1ProducerRelease47
