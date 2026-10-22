import AspisR1ProducerRelease47.Batched48
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def dual.first
  (q : Array field.wide_exact.WideExact 1024#usize)
  (a : field.wide_exact.WideExact)
  (out : Array field.wide_exact.WideExact 256#usize) (i : Std.Usize)
  (left : Std.U16) :
  Result (Array field.wide_exact.WideExact 256#usize)
  := do
  if left = 0#u16
  then ok out
  else
    let i1 ← lift (Std.Usize.wrapping_mul 4#usize i)
    let we ← Array.index_usize q i1
    let i2 ← lift (Std.Usize.wrapping_mul 4#usize i)
    let i3 ← lift (Std.Usize.wrapping_add i2 1#usize)
    let we1 ← Array.index_usize q i3
    let i4 ← lift (Std.Usize.wrapping_mul 4#usize i)
    let i5 ← lift (Std.Usize.wrapping_add i4 2#usize)
    let we2 ← Array.index_usize q i5
    let i6 ← lift (Std.Usize.wrapping_mul 4#usize i)
    let i7 ← lift (Std.Usize.wrapping_add i6 3#usize)
    let we3 ← Array.index_usize q i7
    let we4 ← dual_cell (Array.make 4#usize [ we, we1, we2, we3 ]) a
    let out1 ← Array.update out i we4
    let i8 ← lift (Std.Usize.wrapping_add i 1#usize)
    let i9 ← lift (Std.U16.wrapping_sub left 1#u16)
    dual.first q a out1 i8 i9
partial_fixpoint

def dual.all
  (q : Array field.wide_exact.WideExact 1024#usize)
  (a : field.wide_exact.WideExact) :
  Result (Array field.wide_exact.WideExact 256#usize)
  := do
  let a1 := Array.repeat 256#usize field.wide_exact.WideExact.ZERO
  dual.first q a a1 0#usize 256#u16

end AspisR1ProducerRelease47
