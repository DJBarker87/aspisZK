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
def leaves54.folded_values
  (c : Array field.wide_exact.WideExact 256#usize) (v : Std.Usize) :
  Result (Array field.wide_exact.WideExact 4#usize)
  := do
  let s ← lift (Array.to_slice c)
  let i ← lift (Std.Usize.wrapping_mul 4#usize v)
  let we ← eval_at s i 8#usize
  let s1 ← lift (Array.to_slice c)
  let i1 ← lift (Std.Usize.wrapping_mul 4#usize v)
  let i2 ← lift (Std.Usize.wrapping_add i1 1#usize)
  let we1 ← eval_at s1 i2 8#usize
  let s2 ← lift (Array.to_slice c)
  let i3 ← lift (Std.Usize.wrapping_mul 4#usize v)
  let i4 ← lift (Std.Usize.wrapping_add i3 2#usize)
  let we2 ← eval_at s2 i4 8#usize
  let s3 ← lift (Array.to_slice c)
  let i5 ← lift (Std.Usize.wrapping_mul 4#usize v)
  let i6 ← lift (Std.Usize.wrapping_add i5 3#usize)
  let we3 ← eval_at s3 i6 8#usize
  ok (Array.make 4#usize [ we, we1, we2, we3 ])

def leaves54.column
  (out : Array (Array field.wide_exact.WideExact 29#usize) 4#usize)
  (h : Array field.wide_exact.WideExact 4#usize) (l : Std.Usize)
  (s : Std.Usize) (left : Std.U8) :
  Result (Array (Array field.wide_exact.WideExact 29#usize) 4#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let we ← Array.index_usize h s
    let (a, index_mut_back) ← Array.index_mut_usize out s
    let a1 ← Array.update a l we
    let out1 := index_mut_back a1
    let i ← lift (Std.Usize.wrapping_add s 1#usize)
    let i1 ← lift (Std.U8.wrapping_sub left 1#u8)
    leaves54.column out1 h l i i1
partial_fixpoint

def leaves54.opened
  (c : Array (Array field.wide_exact.WideExact 1024#usize) 29#usize)
  (j : Std.Usize) (l : Std.Usize) (left : Std.U8)
  (out : Array (Array field.wide_exact.WideExact 29#usize) 4#usize) :
  Result (Array (Array field.wide_exact.WideExact 29#usize) 4#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let a ← Array.index_usize c l
    let h ← encode_at a j
    let out1 ← leaves54.column out h l 0#usize 4#u8
    let i ← lift (Std.Usize.wrapping_add l 1#usize)
    let i1 ← lift (Std.U8.wrapping_sub left 1#u8)
    leaves54.opened c j i i1 out1
partial_fixpoint

def leaves54.opened_values
  (c : Array (Array field.wide_exact.WideExact 1024#usize) 29#usize)
  (j : Std.Usize) :
  Result (Array (Array field.wide_exact.WideExact 29#usize) 4#usize)
  := do
  let a := Array.repeat 29#usize field.wide_exact.WideExact.ZERO
  let a1 := Array.repeat 4#usize a
  leaves54.opened c j 0#usize 29#u8 a1

end AspisR1ProducerRelease47
