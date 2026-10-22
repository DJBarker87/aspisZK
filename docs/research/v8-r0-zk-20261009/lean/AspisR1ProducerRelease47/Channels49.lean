import AspisR1ProducerRelease47.Funs
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def channels.sum
  (a : Array field.M31 3#usize) (b : Array field.M31 3#usize) (i : Std.Usize)
  (left : Std.U8) (total : Std.U64) :
  Result Std.U64
  := do
  if left = 0#u8
  then ok total
  else
    let m ← Array.index_usize a i
    let i1 ← lift (core.convert.num.FromU64U32.from m)
    let m1 ← Array.index_usize b i
    let i2 ← lift (core.convert.num.FromU64U32.from m1)
    let product ← lift (core.num.U64.wrapping_mul i1 i2)
    let next ← lift (core.num.U64.wrapping_add total product)
    let i3 ← lift (Std.Usize.wrapping_add i 1#usize)
    let i4 ← lift (Std.U8.wrapping_sub left 1#u8)
    channels.sum a b i3 i4 next
partial_fixpoint

def channels.dot3
  (a : Array field.M31 3#usize) (b : Array field.M31 3#usize) :
  Result field.M31
  := do
  let i ← channels.sum a b 0#usize 3#u8 0#u64
  field.M31.reduce_u64 i

end AspisR1ProducerRelease47
