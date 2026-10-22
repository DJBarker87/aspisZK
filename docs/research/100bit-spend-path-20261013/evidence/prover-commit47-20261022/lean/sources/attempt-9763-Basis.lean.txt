import AspisR1ProducerRelease47.Funs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
@[global_simps, irreducible]
def field.QM31.ONE : field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

@[global_simps, irreducible]
def field.wide_exact.WideExact.ONE : field.wide_exact.WideExact :=
  { c0 := field.QM31.ONE, c1 := field.QM31.ZERO }

def field.wide_exact.WideExact.sub
  (self : field.wide_exact.WideExact) (rhs : field.wide_exact.WideExact) :
  Result field.wide_exact.WideExact
  := do
  let q ← field.QM31.sub self.c0 rhs.c0
  let q1 ← field.QM31.sub self.c1 rhs.c1
  ok { c0 := q, c1 := q1 }

def fill
  (out : Array field.wide_exact.WideExact 512#usize) (j : Std.Usize)
  (left : Std.U16) (width : Std.Usize) (factor : field.wide_exact.WideExact) :
  Result (Array field.wide_exact.WideExact 512#usize)
  := do
  if left = 0#u16
  then ok out
  else
    let we ← Array.index_usize out j
    let we1 ← field.wide_exact.WideExact.mul we factor
    let i ← lift (Std.Usize.wrapping_add width j)
    let out1 ← Array.update out i we1
    let i1 ← lift (Std.Usize.wrapping_add j 1#usize)
    let i2 ← lift (Std.U16.wrapping_sub left 1#u16)
    fill out1 i1 i2 width factor
partial_fixpoint

def stages
  (out : Array field.wide_exact.WideExact 512#usize) (left : Std.U8)
  (width : Std.Usize) (factor : field.wide_exact.WideExact) :
  Result (Array field.wide_exact.WideExact 512#usize)
  := do
  if left = 0#u8
  then ok out
  else
    let i ← lift (UScalar.cast .U16 width)
    let out1 ← fill out 0#usize i width factor
    let square ← field.wide_exact.WideExact.mul factor factor
    let i1 ← lift (Std.U8.wrapping_sub left 1#u8)
    let i2 ← lift (Std.Usize.wrapping_mul width 2#usize)
    let we ← field.wide_exact.WideExact.add square square
    let we1 ←
      field.wide_exact.WideExact.sub we field.wide_exact.WideExact.ONE
    stages out1 i1 i2 we1
partial_fixpoint

def values
  (x : field.wide_exact.WideExact) :
  Result (Array field.wide_exact.WideExact 512#usize)
  := do
  let a := Array.repeat 512#usize field.wide_exact.WideExact.ONE
  stages a 9#u8 1#usize x

end AspisR1ProducerRelease47
