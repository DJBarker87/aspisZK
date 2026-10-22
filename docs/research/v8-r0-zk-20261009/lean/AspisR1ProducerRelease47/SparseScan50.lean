import AspisR1ProducerRelease47.Sparse50
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
def sparse_scan50.one (x : field.QM31) : Result Bool := do
  let i := x.c0.a
  if i = 1#u32
  then
    let i1 := x.c0.b
    if i1 = 0#u32
    then
      let i2 := x.c1.a
      if i2 = 0#u32
      then let i3 := x.c1.b
           ok (i3 = 0#u32)
      else ok false
    else ok false
  else ok false

def sparse_scan50.boolean (x : field.QM31) : Result Bool := do
  let i := x.c0.b
  if i = 0#u32
  then
    let i1 := x.c1.a
    if i1 = 0#u32
    then
      let i2 := x.c1.b
      if i2 = 0#u32
      then let i3 := x.c0.a
           if i3 = 0#u32
           then ok true
           else ok (i3 = 1#u32)
      else ok false
    else ok false
  else ok false

def sparse_scan50.width
  (point : Array field.QM31 10#usize) (left : Std.U8) : Result Std.U8 := do
  if left = 0#u8
  then ok 0#u8
  else
    let n ← lift (Std.U8.wrapping_sub left 1#u8)
    let i ← lift (core.convert.num.FromUsizeU8.from n)
    let value ← Array.index_usize point i
    let b ← sparse_scan50.boolean value
    if b
    then sparse_scan50.width point n
    else ok left
partial_fixpoint

def sparse_scan50.suffix
  (point : Array field.QM31 10#usize) (start : Std.Usize) (left : Std.U8) :
  Result Std.Usize
  := do
  if left = 0#u8
  then ok 0#usize
  else
    let n ← lift (Std.U8.wrapping_sub left 1#u8)
    let prev ← sparse_scan50.suffix point start n
    let i ← lift (core.convert.num.FromUsizeU8.from n)
    let i1 ← lift (core.num.Usize.wrapping_add start i)
    let value ← Array.index_usize point i1
    let i2 ← lift (core.num.Usize.wrapping_shl prev 1#u32)
    let b ← sparse_scan50.one value
    let i3 ← lift (core.convert.num.FromUsizeBool.from b)
    ok (i2 ||| i3)
partial_fixpoint

end AspisR1ProducerRelease47
