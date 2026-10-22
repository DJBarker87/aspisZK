import AspisR1ProducerRelease47.Kernels49
import AspisR1ProducerRelease47.Prepared50
import AspisR1ProducerRelease47.Run50
import AspisR1ProducerRelease47.Dot50
import AspisR1ProducerRelease47.Totals50
import AspisR1ProducerRelease47.Reconstruction49
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def sparse50.factor
  (value : field.QM31) (bit : Std.Usize) : Result field.QM31 := do
  if bit = 0#usize
  then field.QM31.sub field.QM31.ONE value
  else ok value

def sparse50.weight
  (point : Array field.QM31 10#usize) (prefix1 : Std.Usize) (width : Std.U8)
  (i : Std.Usize) (left : Std.U8) (acc : field.QM31) :
  Result field.QM31
  := do
  if left = 0#u8
  then ok acc
  else
    let i1 ← lift (core.convert.num.FromUsizeU8.from width)
    let i2 ← lift (core.num.Usize.wrapping_sub i1 1#usize)
    let shift ← lift (core.num.Usize.wrapping_sub i2 i)
    let i3 ← lift (UScalar.cast .U32 shift)
    let i4 ← lift (core.num.Usize.wrapping_shr prefix1 i3)
    let bit ← lift (i4 &&& 1#usize)
    let value ← Array.index_usize point i
    let factor ← sparse50.factor value bit
    let i5 ← lift (core.num.Usize.wrapping_add i 1#usize)
    let i6 ← lift (Std.U8.wrapping_sub left 1#u8)
    let q ← field.QM31.mul acc factor
    sparse50.weight point prefix1 width i5 i6 q
partial_fixpoint

def sparse50.row
  (prefix1 : Std.Usize) (trailing : Std.U8) (suffix : Std.Usize) :
  Result Std.Usize
  := do
  let i ← lift (core.convert.num.FromU32U8.from trailing)
  let i1 ← lift (core.num.Usize.wrapping_shl prefix1 i)
  ok (i1 ||| suffix)

end AspisR1ProducerRelease47
