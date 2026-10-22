import AspisR1ProducerRelease47.Basis
import AspisR1ProducerRelease47.Pairs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def power_fill
  {N : Std.Usize} (out : Array field.wide_exact.WideExact N)
  (x : field.wide_exact.WideExact) (p : field.wide_exact.WideExact)
  (i : Std.Usize) (left : Std.U8) :
  Result (Array field.wide_exact.WideExact N)
  := do
  if left = 0#u8
  then ok out
  else
    let (_, index_mut_back) ← Array.index_mut_usize out i
    if left = 1#u8
    then ok (index_mut_back p)
    else
      let out1 := index_mut_back p
      let we ← field.wide_exact.WideExact.mul p x
      let i1 ← lift (Std.Usize.wrapping_add i 1#usize)
      let i2 ← lift (Std.U8.wrapping_sub left 1#u8)
      power_fill out1 x we i1 i2
partial_fixpoint

def gamma
  (x : field.wide_exact.WideExact) :
  Result (Array field.wide_exact.WideExact 29#usize)
  := do
  let a := Array.repeat 29#usize field.wide_exact.WideExact.ZERO
  power_fill a x field.wide_exact.WideExact.ONE 0#usize 29#u8

def kappa
  (x : field.wide_exact.WideExact) :
  Result (Array field.wide_exact.WideExact 7#usize)
  := do
  let a := Array.repeat 7#usize field.wide_exact.WideExact.ZERO
  power_fill a x field.wide_exact.WideExact.ONE 0#usize 7#u8

end AspisR1ProducerRelease47
