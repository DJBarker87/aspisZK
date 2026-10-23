import AspisR1ProducerRelease47.Basis
/-! Extracted counter owner, with identical arithmetic callees rebound to the
previously proved release extraction. bind-counter.py checks every reused
callee declaration body byte-for-byte. No external template is installed. -/
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1ProducerRelease47
def Boundary49.sum
  (q : Array Std.U32 28#usize) (i : Std.Usize) (left : Std.U8)
  (total : Std.U64) :
  Result Std.U64
  := do
  if left = 0#u8
  then ok total
  else
    let i1 ← Array.index_usize q i
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let next ← lift (Std.U64.wrapping_add total i2)
    let i3 ← lift (Std.Usize.wrapping_add i 1#usize)
    let i4 ← lift (Std.U8.wrapping_sub left 1#u8)
    Boundary49.sum q i3 i4 next
partial_fixpoint

def Boundary49.limb (q : Array Std.U32 28#usize) : Result field.M31 := do
  let i ← Array.index_usize q 0#usize
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let initial ← lift (Std.U64.wrapping_mul 2#u64 i1)
  let i2 ← Boundary49.sum q 1#usize 27#u8 initial
  field.M31.reduce_u64 i2

end AspisR1ProducerRelease47
