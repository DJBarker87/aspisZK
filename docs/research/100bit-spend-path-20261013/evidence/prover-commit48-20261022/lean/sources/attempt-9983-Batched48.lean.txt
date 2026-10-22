import AspisR1ProducerRelease47.Basis
import AspisR1ProducerRelease47.Pairs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def field.CM31.mul_m31
  (self : field.CM31) (rhs : field.M31) : Result field.CM31 := do
  let m ← field.M31.mul self.a rhs
  let m1 ← field.M31.mul self.b rhs
  ok { a := m, b := m1 }

def field.QM31.mul_m31
  (self : field.QM31) (rhs : field.M31) : Result field.QM31 := do
  let c ← field.CM31.mul_m31 self.c0 rhs
  let c1 ← field.CM31.mul_m31 self.c1 rhs
  ok { c0 := c, c1 }

def field.wide_exact.WideExact.mul_m31
  (self : field.wide_exact.WideExact) (rhs : field.M31) :
  Result field.wide_exact.WideExact
  := do
  let i ← rhs % field.P
  let q ← field.QM31.mul_m31 self.c0 i
  let q1 ← field.QM31.mul_m31 self.c1 i
  ok { c0 := q, c1 := q1 }

def scalar
  (x : field.wide_exact.WideExact) (y : field.M31) :
  Result field.wide_exact.WideExact
  := do
  field.wide_exact.WideExact.mul_m31 x y

def dual_cell
  (h : Array field.wide_exact.WideExact 4#usize)
  (alpha : field.wide_exact.WideExact) :
  Result field.wide_exact.WideExact
  := do
  let we ← Array.index_usize h 0#usize
  let we1 ← Array.index_usize h 3#usize
  let we2 ← Array.index_usize h 2#usize
  let we3 ← Array.index_usize h 1#usize
  let we4 ← field.wide_exact.WideExact.mul alpha we3
  let we5 ← field.wide_exact.WideExact.add we2 we4
  let we6 ← field.wide_exact.WideExact.mul alpha we5
  let we7 ← field.wide_exact.WideExact.add we1 we6
  let we8 ← field.wide_exact.WideExact.mul alpha we7
  let we9 ← field.wide_exact.WideExact.add we we8
  field.wide_exact.WideExact.mul_m31 we9 536870912#u32

def round_step
  (q : Array field.wide_exact.WideExact 1024#usize)
  (w : Array field.wide_exact.WideExact 1024#usize)
  (out : Array field.wide_exact.WideExact 7#usize) (d : Std.Usize)
  (s : Std.Usize) (t : Std.Usize) :
  Result (Array field.wide_exact.WideExact 7#usize)
  := do
  let i ←
    Array.index_usize
      (Array.make 4#usize [ 0#usize, 3#usize, 2#usize, 1#usize ]) t
  let k ← lift (Std.Usize.wrapping_add s i)
  let we ← Array.index_usize out k
  let i1 ← lift (Std.Usize.wrapping_mul 4#usize d)
  let i2 ← lift (Std.Usize.wrapping_add i1 s)
  let we1 ← Array.index_usize q i2
  let i3 ← lift (Std.Usize.wrapping_mul 4#usize d)
  let i4 ← lift (Std.Usize.wrapping_add i3 t)
  let we2 ← Array.index_usize w i4
  let we3 ← field.wide_exact.WideExact.mul we1 we2
  let we4 ← field.wide_exact.WideExact.add we we3
  Array.update out k we4

def roots
  (x : field.wide_exact.WideExact) (y : field.M31)
  (h : Array field.wide_exact.WideExact 4#usize)
  (q : Array field.wide_exact.WideExact 1024#usize)
  (w : Array field.wide_exact.WideExact 1024#usize)
  (out : Array field.wide_exact.WideExact 7#usize) (d : Std.Usize)
  (s : Std.Usize) (t : Std.Usize) :
  Result (field.wide_exact.WideExact × field.wide_exact.WideExact × (Array
    field.wide_exact.WideExact 7#usize))
  := do
  let we ← scalar x y
  let we1 ← dual_cell h x
  let a ← round_step q w out d s t
  ok (we, we1, a)

end AspisR1ProducerRelease47
