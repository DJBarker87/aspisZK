import AspisR1ProducerRelease47.Funs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
@[global_simps, irreducible]
def field.wide_exact.WideExact.ZERO : field.wide_exact.WideExact :=
  { c0 := field.QM31.ZERO, c1 := field.QM31.ZERO }

def pairs
  (q : Array field.wide_exact.WideExact 1024#usize)
  (basis : Array field.wide_exact.WideExact 512#usize) (i : Std.Usize)
  (left : Std.U16) (p0 : field.wide_exact.WideExact)
  (p1 : field.wide_exact.WideExact) :
  Result (field.wide_exact.WideExact × field.wide_exact.WideExact)
  := do
  if left = 0#u16
  then ok (p0, p1)
  else
    let n ← Array.index_usize basis i
    let i1 ← lift (Std.Usize.wrapping_mul 2#usize i)
    let we ← Array.index_usize q i1
    let we1 ← field.wide_exact.WideExact.mul we n
    let p01 ← field.wide_exact.WideExact.add p0 we1
    let i2 ← lift (Std.Usize.wrapping_mul 2#usize i)
    let i3 ← lift (Std.Usize.wrapping_add i2 1#usize)
    let we2 ← Array.index_usize q i3
    let we3 ← field.wide_exact.WideExact.mul we2 n
    let p11 ← field.wide_exact.WideExact.add p1 we3
    let i4 ← lift (Std.Usize.wrapping_add i 1#usize)
    let i5 ← lift (Std.U16.wrapping_sub left 1#u16)
    pairs q basis i4 i5 p01 p11
partial_fixpoint

def evaluate
  (q : Array field.wide_exact.WideExact 1024#usize)
  (basis : Array field.wide_exact.WideExact 512#usize)
  (y : field.wide_exact.WideExact) :
  Result field.wide_exact.WideExact
  := do
  let (p0, p1) ←
    pairs q basis 0#usize 512#u16 field.wide_exact.WideExact.ZERO
      field.wide_exact.WideExact.ZERO
  let we ← field.wide_exact.WideExact.mul y p1
  field.wide_exact.WideExact.add p0 we

end AspisR1ProducerRelease47
