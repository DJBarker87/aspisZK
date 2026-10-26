import JFs_TX2_Outer
import JFs_TX2_FromLimbs
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFs_TX2_DotSuffix
open Aeneas Aeneas.Std Result
open FIp_NativeDots

def scalarFinish (limbs : Array U64 8#usize) : Result FIo_Install.NE := do
  let i ← Array.index_usize limbs 0#usize
  let m ← FIo_Native.aspis_core.field.M31.reduce_u64 i
  let i1 ← Array.index_usize limbs 1#usize
  let m1 ← FIo_Native.aspis_core.field.M31.reduce_u64 i1
  let i2 ← Array.index_usize limbs 2#usize
  let m2 ← FIo_Native.aspis_core.field.M31.reduce_u64 i2
  let i3 ← Array.index_usize limbs 3#usize
  let m3 ← FIo_Native.aspis_core.field.M31.reduce_u64 i3
  let i4 ← Array.index_usize limbs 4#usize
  let m4 ← FIo_Native.aspis_core.field.M31.reduce_u64 i4
  let i5 ← Array.index_usize limbs 5#usize
  let m5 ← FIo_Native.aspis_core.field.M31.reduce_u64 i5
  let i6 ← Array.index_usize limbs 6#usize
  let m6 ← FIo_Native.aspis_core.field.M31.reduce_u64 i6
  let i7 ← Array.index_usize limbs 7#usize
  let m7 ← FIo_Native.aspis_core.field.M31.reduce_u64 i7
  let o ←
    FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [ m, m1, m2, m3, m4, m5, m6, m7 ])
  let value ← core.option.Option.unwrap o
  ok value

def tail (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize) (slot : Usize) : Result FIo_Install.NE := do
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
  let (r, tail1) ← FIo_Native.fast_pairing.EbyKDot.push tail we q1
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
  let (r1, tail2) ← FIo_Native.fast_pairing.EbyKDot.push tail1 we1 q2
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
  let (r2, tail3) ← FIo_Native.fast_pairing.EbyKDot.push tail2 we2 q3
  core.result.Result.unwrap core.fmt.DebugUnit r2
  let we3 ← FIo_Native.fast_pairing.EbyKDot.finish tail3
  ok we3

theorem body (q : Array U8 608#usize) (g : Array FIo_Install.NE 29#usize) (slot : Usize) :
    fast_dots.four_dots_one q g slot=
      (do let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
            (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
            {start:=0#usize,«end»:=26#usize} 4#usize
          let limbs ← fast_dots.four_dots_one_loop0 iter q g slot (Array.repeat 8#usize 0#u64)
          let head ← scalarFinish limbs
          let tail ← tail q g slot
          FIo_Native.aspis_core.field.wide_exact.WideExact.add head tail) := by
  simp only [fast_dots.four_dots_one,scalarFinish,tail,bind_assoc_eq,bind_tc_ok]

#print axioms body
end AspisR1.JFs_TX2_DotSuffix
end
