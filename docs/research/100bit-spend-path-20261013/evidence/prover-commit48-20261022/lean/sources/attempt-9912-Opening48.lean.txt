import AspisR1ProducerRelease47.Funs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def mix
  (coefficients : Array field.wide_exact.WideExact 29#usize)
  (powers : Array field.wide_exact.WideExact 29#usize) (i : Std.Usize)
  (left : Std.U8) (sum : field.wide_exact.WideExact) :
  Result field.wide_exact.WideExact
  := do
  if left = 0#u8
  then ok sum
  else
    let we ← Array.index_usize powers i
    let we1 ← Array.index_usize coefficients i
    let we2 ← field.wide_exact.WideExact.mul we we1
    let next ← field.wide_exact.WideExact.add sum we2
    let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
    let i2 ← lift (Std.U8.wrapping_sub left 1#u8)
    mix coefficients powers i1 i2 next
partial_fixpoint

def fold_cell
  (h : Array field.wide_exact.WideExact 4#usize)
  (alpha : field.wide_exact.WideExact) :
  Result field.wide_exact.WideExact
  := do
  let we ← Array.index_usize h 0#usize
  let we1 ← Array.index_usize h 1#usize
  let we2 ← Array.index_usize h 2#usize
  let we3 ← Array.index_usize h 3#usize
  let we4 ← field.wide_exact.WideExact.mul alpha we3
  let we5 ← field.wide_exact.WideExact.add we2 we4
  let we6 ← field.wide_exact.WideExact.mul alpha we5
  let we7 ← field.wide_exact.WideExact.add we1 we6
  let we8 ← field.wide_exact.WideExact.mul alpha we7
  field.wide_exact.WideExact.add we we8

def fold_first
  (q : Array field.wide_exact.WideExact 1024#usize)
  (alpha : field.wide_exact.WideExact)
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
    let we4 ← fold_cell (Array.make 4#usize [ we, we1, we2, we3 ]) alpha
    let out1 ← Array.update out i we4
    let i8 ← lift (Std.Usize.wrapping_add i 1#usize)
    let i9 ← lift (Std.U16.wrapping_sub left 1#u16)
    fold_first q alpha out1 i8 i9
partial_fixpoint

def fold_second
  (q : Array field.wide_exact.WideExact 256#usize)
  (alpha : field.wide_exact.WideExact)
  (out : Array field.wide_exact.WideExact 64#usize) (i : Std.Usize)
  (left : Std.U8) :
  Result (Array field.wide_exact.WideExact 64#usize)
  := do
  if left = 0#u8
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
    let we4 ← fold_cell (Array.make 4#usize [ we, we1, we2, we3 ]) alpha
    let out1 ← Array.update out i we4
    let i8 ← lift (Std.Usize.wrapping_add i 1#usize)
    let i9 ← lift (Std.U8.wrapping_sub left 1#u8)
    fold_second q alpha out1 i8 i9
partial_fixpoint

end AspisR1ProducerRelease47
