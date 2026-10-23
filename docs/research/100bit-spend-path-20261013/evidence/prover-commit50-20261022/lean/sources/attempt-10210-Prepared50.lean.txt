import AspisR1ProducerRelease47.Dot50
import AspisR1ProducerRelease47.Totals50
import AspisR1ProducerRelease47.Reconstruction49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def prepared50.prepare
  (x : field.QM31) : Result (Array (Array field.M31 3#usize) 3#usize) := do
  let a ← dot50.prepare_c x.c0
  let b ← dot50.prepare_c x.c1
  let c ← field.CM31.add x.c0 x.c1
  let c1 ← dot50.prepare_c c
  ok (Array.make 3#usize [ a, b, c1 ])

def prepared50.cm
  (left : Array field.M31 3#usize) (right : field.CM31) :
  Result field.CM31
  := do
  let m ← Array.index_usize left 0#usize
  let m0 ← field.M31.mul m right.a
  let m1 ← Array.index_usize left 1#usize
  let m11 ← field.M31.mul m1 right.b
  let m2 ← Array.index_usize left 2#usize
  let m3 ← field.M31.add right.a right.b
  let m21 ← field.M31.mul m2 m3
  let m4 ← field.M31.sub m0 m11
  let m5 ← field.M31.sub m21 m0
  let m6 ← field.M31.sub m5 m11
  ok { a := m4, b := m6 }

def prepared50.combine
  (m0 : field.CM31) (m1 : field.CM31) (m2 : field.CM31) :
  Result field.QM31
  := do
  let c ← reconstruction.mul_r m1
  let c1 ← field.CM31.add m0 c
  let c2 ← field.CM31.sub m2 m0
  let c3 ← field.CM31.sub c2 m1
  ok { c0 := c1, c1 := c3 }

def prepared50.mul
  (left : Array (Array field.M31 3#usize) 3#usize) (right : field.QM31) :
  Result field.QM31
  := do
  let a ← Array.index_usize left 0#usize
  let m0 ← prepared50.cm a right.c0
  let a1 ← Array.index_usize left 1#usize
  let m1 ← prepared50.cm a1 right.c1
  let a2 ← Array.index_usize left 2#usize
  let c ← field.CM31.add right.c0 right.c1
  let m2 ← prepared50.cm a2 c
  prepared50.combine m0 m1 m2

end AspisR1ProducerRelease47
