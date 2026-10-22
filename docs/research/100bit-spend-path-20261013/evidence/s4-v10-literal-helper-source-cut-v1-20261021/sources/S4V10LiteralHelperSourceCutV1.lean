import S4V10FactoredHelperTransportV1
import AspisR1FastDotsCurrent.FunsOpsFixedV6
import S4FixedTailProgramEqualityRootV1
import S4WholeHelperTransferRootV1

open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1FastDotsV10LiteralHelperSourceCutV1
open AspisR1FastDotsV10FactoredHelperTransportV1
open AspisR1FastDotsV10HeadValueTransportV1
open AspisR1FastDotsV10HeadLoopBoundV1
open AspisR1FastDotsV10CarrierMapV1
abbrev CurrentOps := AspisR1FastDotsCurrent.FourDotsOps
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact
abbrev V10QM := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.QM31
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Usize := Aeneas.Std.Usize
abbrev U32 := Aeneas.Std.U32

private theorem result_bind_assoc {A B C : Type} (r : Result A)
    (f : A → Result B) (k : B → Result C) :
    ((r >>= f) >>= k) = (r >>= fun x => f x >>= k) := by
  cases r <;> rfl

def literalFromLimbs (ops : CurrentOps) (limbs : Array U32 8#usize) : Result (Option V10Wide) := do
  let o ← ops.wideFromLimbs limbs
  ok (o.map wideFromEbyK)

def literalQMFromBytes (ops : CurrentOps) (s : Slice Std.U8) : Result (Option V10QM) := do
  let o ← ops.qm31FromBytes s
  ok (o.map qm31FromEbyK)

def literalPush (ops : CurrentOps) (tail : AspisR1FastDotsCurrent.fast_pairing.EbyKDot)
    (w : V10Wide) (q : V10QM) :
    Result ((core.result.Result Unit Unit) × AspisR1FastDotsCurrent.fast_pairing.EbyKDot) :=
  ops.ebyKPush tail (wideToEbyK w) (qm31ToEbyK q)

def literalFinish (ops : CurrentOps) (tail : AspisR1FastDotsCurrent.fast_pairing.EbyKDot) : Result V10Wide :=
  AspisR1FastDotsV10FactoredHelperTransportV1.mapRes wideFromEbyK (ops.ebyKFinish tail)

def literalAdd (ops : CurrentOps) (x y : V10Wide) : Result V10Wide :=
  AspisR1FastDotsV10FactoredHelperTransportV1.mapRes wideFromEbyK
    (ops.wideAdd (wideToEbyK x) (wideToEbyK y))

/-- Literal typed source cut of the emitted V10 `four_dots_one` body. Calls to
    extracted external functions are represented by the named `ops` slots above;
    the loop and all arithmetic/effect order are copied from generated Funs.lean. -/
def literalV10Helper (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) : Result V10Wide := do
  let limbs := Array.repeat 8#usize 0#u64
  let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := 26#usize } 4#usize
  let limbs1 ← v10HeadLoop ops iter q g slot limbs
  let i ← Array.index_usize limbs1 0#usize
  let m ← ops.m31ReduceU64 i
  let i1 ← Array.index_usize limbs1 1#usize
  let m1 ← ops.m31ReduceU64 i1
  let i2 ← Array.index_usize limbs1 2#usize
  let m2 ← ops.m31ReduceU64 i2
  let i3 ← Array.index_usize limbs1 3#usize
  let m3 ← ops.m31ReduceU64 i3
  let i4 ← Array.index_usize limbs1 4#usize
  let m4 ← ops.m31ReduceU64 i4
  let i5 ← Array.index_usize limbs1 5#usize
  let m5 ← ops.m31ReduceU64 i5
  let i6 ← Array.index_usize limbs1 6#usize
  let m6 ← ops.m31ReduceU64 i6
  let i7 ← Array.index_usize limbs1 7#usize
  let m7 ← ops.m31ReduceU64 i7
  let o ← literalFromLimbs ops (Array.make 8#usize [m,m1,m2,m3,m4,m5,m6,m7])
  let value ← core.option.Option.unwrap o
  let tail ← ops.ebyKNew
  let we ← Array.index_usize g 28#usize
  let i8 ← slot * 120#usize
  let i9 ← i8 + 104#usize
  let i10 ← i8 + 120#usize
  let s ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q { start := i9, «end» := i10 }
  let o1 ← literalQMFromBytes ops s
  let q1 ← core.option.Option.unwrap o1
  let (r,tail1) ← literalPush ops tail we q1
  core.result.Result.unwrap core.fmt.DebugUnit r
  let i11 ← slot * 32#usize
  let i12 ← 480#usize + i11
  let i13 ← 0#usize * 16#usize
  let offset0 ← i12 + i13
  let i14 ← 0#usize + 26#usize
  let we1 ← Array.index_usize g i14
  let i15 ← offset0 + 16#usize
  let s1 ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q { start := offset0, «end» := i15 }
  let o2 ← literalQMFromBytes ops s1
  let q2 ← core.option.Option.unwrap o2
  let (r1,tail2) ← literalPush ops tail1 we1 q2
  core.result.Result.unwrap core.fmt.DebugUnit r1
  let i16 ← 480#usize + i11
  let i17 ← 1#usize * 16#usize
  let offset1 ← i16 + i17
  let i18 ← 1#usize + 26#usize
  let we2 ← Array.index_usize g i18
  let i19 ← offset1 + 16#usize
  let s2 ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q { start := offset1, «end» := i19 }
  let o3 ← literalQMFromBytes ops s2
  let q3 ← core.option.Option.unwrap o3
  let (r2,tail3) ← literalPush ops tail2 we2 q3
  core.result.Result.unwrap core.fmt.DebugUnit r2
  let we3 ← literalFinish ops tail3
  literalAdd ops value we3

theorem literal_helper_eq_factored (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) :
    literalV10Helper ops q g slot = v10FactoredHelper ops q g slot := by
  -- This is only the cut at the head value boundary; keep the Result effects in
  -- source order and unfold the named operation adapters at that boundary.
  unfold literalV10Helper
  unfold AspisR1FastDotsV10FactoredHelperTransportV1.v10FactoredHelper
  unfold AspisR1FastDotsV10TailMapRootV1.v10Tail
  unfold AspisR1FastDotsV10TailMapRootV1.v10QMFromBytes
    AspisR1FastDotsV10TailMapRootV1.v10Push
    AspisR1FastDotsV10TailMapRootV1.v10Finish
    AspisR1FastDotsV10TailMapRootV1.v10Add
    literalFromLimbs literalQMFromBytes literalPush literalFinish literalAdd
    AspisR1FastDotsV10HeadValueTransportV1.v10HeadValue
    AspisR1FastDotsV10HeadValueTransportV1.v10HeadPack
    AspisR1FastDotsV10HeadValueTransportV1.reduceHeadLimbs
    AspisR1FastDotsV10TailMapRootV1.mapRes
    AspisR1FastDotsV10FactoredHelperTransportV1.mapRes
  simp only [result_bind_assoc, bind_tc_ok]
  rfl

theorem fixed_factored_helper_eq_current (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) :
    AspisR1FastDotsV10FactoredHelperTransportV1.fixedFactoredHelper ops q g slot =
      AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q
        (AspisR1FastDotsV10TypedInnerBodyOpsV1.mapWideArray g) slot := by
  rw [AspisR1FastDotsWholeHelperTransferRootV1.fixed_helper_eq_grouped]
  unfold AspisR1FastDotsV10FactoredHelperTransportV1.fixedFactoredHelper
    AspisR1FastDotsV10HeadValueTransportV1.fixedHeadValue
    AspisR1FastDotsV10HeadValueTransportV1.fixedHeadPack
    AspisR1FastDotsV10HeadValueTransportV1.reduceHeadLimbs
    AspisR1FastDotsWholeHelperTransferRootV1.groupedFixed
    AspisR1FastDotsLiteralN8PackingRootV1.literalEight
    AspisR1FastDotsLiteralN8PackingRootV1.readReduce
  simp only [result_bind_assoc, bind_tc_ok]

theorem literal_helper_eq_fixed (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) :
    literalV10Helper ops q g slot =
      AspisR1FastDotsV10FactoredHelperTransportV1.mapRes wideFromEbyK
        (AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q
          (AspisR1FastDotsV10TypedInnerBodyOpsV1.mapWideArray g) slot) := by
  calc
    literalV10Helper ops q g slot =
        AspisR1FastDotsV10FactoredHelperTransportV1.v10FactoredHelper ops q g slot :=
      literal_helper_eq_factored ops q g slot
    _ = AspisR1FastDotsV10FactoredHelperTransportV1.mapRes wideFromEbyK
          (AspisR1FastDotsV10FactoredHelperTransportV1.fixedFactoredHelper ops q g slot) :=
      AspisR1FastDotsV10FactoredHelperTransportV1.factored_helper_eq_fixed ops q g slot
    _ = AspisR1FastDotsV10FactoredHelperTransportV1.mapRes wideFromEbyK
          (AspisR1FastDotsCurrent.fast_dots.four_dots_one ops q
            (AspisR1FastDotsV10TypedInnerBodyOpsV1.mapWideArray g) slot) :=
      congrArg (AspisR1FastDotsV10FactoredHelperTransportV1.mapRes wideFromEbyK)
        (fixed_factored_helper_eq_current ops q g slot)

#print axioms literal_helper_eq_factored
#print axioms fixed_factored_helper_eq_current
#print axioms literal_helper_eq_fixed
end AspisR1FastDotsV10LiteralHelperSourceCutV1
