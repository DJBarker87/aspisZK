import NFF_LoggedPush
import NFE_NFA_SuffixFactor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFF_LoggedTail
open Aeneas Aeneas.Std Result
def run (oracle : NFF_ProductCall.Oracle) (q : Array U8 608#usize) (g : Array NEV_DotCarrier.NE 29#usize) (slot : Usize) : Result NEV_DotCarrier.NE := do
  let tail ← FIo_Native.fast_pairing.EbyKDot.new
  let we ← Array.index_usize g 28#usize
  let i8 ← slot * 120#usize
  let i9 ← i8 + 104#usize
  let i10 ← i8 + 120#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := i9, «end» := i10 }
  let o1 ← AspisR1.FIp_DotDecode.field.QM31.from_le_bytes s
  let q1 ← core.option.Option.unwrap o1
  let (r, tail1) ← NFF_LoggedPush.publicPush oracle tail we q1
  core.result.Result.unwrap core.fmt.DebugUnit r
  let i11 ← slot * 32#usize
  let i12 ← 480#usize + i11
  let i13 ← 0#usize * 16#usize
  let offset0 ← i12 + i13
  let i14 ← 0#usize + 26#usize
  let we1 ← Array.index_usize g i14
  let i15 ← offset0 + 16#usize
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := offset0, «end» := i15 }
  let o2 ← AspisR1.FIp_DotDecode.field.QM31.from_le_bytes s1
  let q2 ← core.option.Option.unwrap o2
  let (r1, tail2) ← NFF_LoggedPush.publicPush oracle tail1 we1 q2
  core.result.Result.unwrap core.fmt.DebugUnit r1
  let i16 ← 480#usize + i11
  let i17 ← 1#usize * 16#usize
  let offset1 ← i16 + i17
  let i18 ← 1#usize + 26#usize
  let we2 ← Array.index_usize g i18
  let i19 ← offset1 + 16#usize
  let s2 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := offset1, «end» := i19 }
  let o3 ← AspisR1.FIp_DotDecode.field.QM31.from_le_bytes s2
  let q3 ← core.option.Option.unwrap o3
  let (r2, tail3) ← NFF_LoggedPush.publicPush oracle tail2 we2 q3
  core.result.Result.unwrap core.fmt.DebugUnit r2
  let we3 ← FIo_Native.fast_pairing.EbyKDot.finish tail3
  ok we3


theorem replay (oracle : NFF_ProductCall.Oracle) (law : NFF_ProductCall.Law oracle)
    (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) :
    run oracle q g slot=NFE_NFA_SuffixFactor.tail q g slot := by
  simp only [run,NFE_NFA_SuffixFactor.tail,NFF_LoggedPush.public_replay oracle law]

#print axioms replay
end AspisR1.NFF_LoggedTail
end
