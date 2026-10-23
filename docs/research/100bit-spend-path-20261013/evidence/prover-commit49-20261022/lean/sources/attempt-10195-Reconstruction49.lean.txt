import AspisR1ProducerRelease47.Funs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def reconstruction.cm (s : Array Std.U64 3#usize) : Result field.CM31 := do
  let i ← Array.index_usize s 0#usize
  let m0 ← field.M31.reduce_u64 i
  let i1 ← Array.index_usize s 1#usize
  let m1 ← field.M31.reduce_u64 i1
  let i2 ← Array.index_usize s 2#usize
  let m2 ← field.M31.reduce_u64 i2
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { a := m, b := m4 }

def reconstruction.mul_r (x : field.CM31) : Result field.CM31 := do
  let two_a ← field.M31.double x.a
  let real ← field.M31.sub two_a x.b
  let two_b ← field.M31.double x.b
  let imag ← field.M31.add x.a two_b
  ok { a := real, b := imag }

def reconstruction.q
  (s : Array (Array Std.U64 3#usize) 3#usize) : Result field.QM31 := do
  let a ← Array.index_usize s 0#usize
  let m0 ← reconstruction.cm a
  let a1 ← Array.index_usize s 1#usize
  let m1 ← reconstruction.cm a1
  let a2 ← Array.index_usize s 2#usize
  let m2 ← reconstruction.cm a2
  let c ← reconstruction.mul_r m1
  let c1 ← field.CM31.add m0 c
  let c2 ← field.CM31.sub m2 m0
  let c3 ← field.CM31.sub c2 m1
  ok { c0 := c1, c1 := c3 }

end AspisR1ProducerRelease47
