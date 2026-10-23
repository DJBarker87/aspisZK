import AspisR1ProducerRelease47.Basis
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def stored.product
  (rows : Array (Array field.QM31 4#usize) 5#usize) (j : Std.Usize)
  (d : Std.Usize) (left : Std.U8) (acc : field.QM31) :
  Result field.QM31
  := do
  if left = 0#u8
  then ok acc
  else
    let i ← lift (Std.Usize.wrapping_mul 2#usize d)
    let i1 ← lift (UScalar.cast .U32 i)
    let i2 ← lift (Std.Usize.wrapping_shr j i1)
    let digit ← lift (i2 &&& 3#usize)
    let a ← Array.index_usize rows d
    let q ← Array.index_usize a digit
    let next ← field.QM31.mul acc q
    let i3 ← lift (Std.Usize.wrapping_add d 1#usize)
    let i4 ← lift (Std.U8.wrapping_sub left 1#u8)
    stored.product rows j i3 i4 next
partial_fixpoint

end AspisR1ProducerRelease47
