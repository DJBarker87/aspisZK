import AspisR1ProducerRelease47.Funs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def horner
  (q : Array field.QM31 1024#usize) (offset : Std.Usize) (left : Std.U8)
  (x : field.QM31) (sum : field.QM31) :
  Result field.QM31
  := do
  if left = 0#u8
  then ok sum
  else
    let j ← lift (Std.U8.wrapping_sub left 1#u8)
    let q1 ← field.QM31.mul sum x
    let i ← lift (UScalar.cast .Usize j)
    let i1 ← lift (Std.Usize.wrapping_add offset i)
    let q2 ← Array.index_usize q i1
    let next ← field.QM31.add q1 q2
    let i2 ← lift (Std.U8.wrapping_sub left 1#u8)
    horner q offset i2 x next
partial_fixpoint

def extra
  (q : Array field.QM31 1024#usize) (a : field.QM31) (b : field.QM31) :
  Result field.QM31
  := do
  let left ← horner q 0#usize 28#u8 a field.QM31.ZERO
  let right ← horner q 28#usize 28#u8 b field.QM31.ZERO
  let q1 ← field.QM31.add field.QM31.ZERO left
  field.QM31.add q1 right

end AspisR1ProducerRelease47
