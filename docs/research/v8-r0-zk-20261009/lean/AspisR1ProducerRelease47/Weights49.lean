import AspisR1ProducerRelease47.Basis
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def field.wide_exact.WideExact.mul_qm31
  (self : field.wide_exact.WideExact) (rhs : field.QM31) :
  Result field.wide_exact.WideExact
  := do
  let rhs1 ← field.wide_exact.canonical_qm31 rhs
  let q ← field.QM31.mul self.c0 rhs1
  let q1 ← field.QM31.mul self.c1 rhs1
  ok { c0 := q, c1 := q1 }

def owned.cell
  (kp : Array field.wide_exact.WideExact 7#usize)
  (raw1 : Array field.QM31 7#usize) (kind : Std.Usize) (left : Std.U8)
  (sum : field.wide_exact.WideExact) :
  Result field.wide_exact.WideExact
  := do
  if left = 0#u8
  then ok sum
  else
    let we ← Array.index_usize kp kind
    let q ← Array.index_usize raw1 kind
    let we1 ← field.wide_exact.WideExact.mul_qm31 we q
    let next ← field.wide_exact.WideExact.add sum we1
    let i ← lift (Std.Usize.wrapping_add kind 1#usize)
    let i1 ← lift (Std.U8.wrapping_sub left 1#u8)
    owned.cell kp raw1 i i1 next
partial_fixpoint

def owned.inactive
  (q : Array field.wide_exact.WideExact 1024#usize)
  (raw1 : Array field.QM31 1024#usize) (j : Std.Usize) (left : Std.U16)
  (sum : field.wide_exact.WideExact) :
  Result field.wide_exact.WideExact
  := do
  if left = 0#u16
  then ok sum
  else
    let we ← Array.index_usize q j
    let q1 ← Array.index_usize raw1 j
    let we1 ← field.wide_exact.WideExact.mul_qm31 we q1
    let next ← field.wide_exact.WideExact.add sum we1
    let i ← lift (Std.Usize.wrapping_add j 1#usize)
    let i1 ← lift (Std.U16.wrapping_sub left 1#u16)
    owned.inactive q raw1 i i1 next
partial_fixpoint

end AspisR1ProducerRelease47
