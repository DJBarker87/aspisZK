import AspisR1FastDotsMinimalFixedCallsV10.Types
import AspisR1FastDotsCurrent.FunsOpsV4
import AspisR1FastDotsCurrent.FunsOpsFixedV6
import EbyKPushExplicitTypesV1
import S4V10CarrierMapV1

open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1FastDotsV10TypedInnerBodyOpsV1

open AspisR1FastDotsV10CarrierMapV1
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact
abbrev CurrentOps := AspisR1FastDotsCurrent.FourDotsOps

structure BodyOps where
  m31FromBytes : Array Std.U8 4#usize → Result (Option AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.M31)
  wideToLimbs : V10Wide → Result (Array Std.U32 8#usize)

def adaptOps (ops : CurrentOps) : BodyOps where
  m31FromBytes := ops.m31FromBytes
  wideToLimbs := fun w => ops.wideToLimbs (wideToEbyK w)


def mapWideArray {N : Aeneas.Std.Usize} (g : Aeneas.Std.Array V10Wide N) :
    Aeneas.Std.Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact N :=
  ⟨List.map wideToEbyK g.val, by simpa using g.property⟩

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem bind_mapResult {A B C : Type} (f : A → B) (r : Result A)
    (k : B → Result C) :
    Bind.bind (mapResult f r) k = Bind.bind r (fun x => k (f x)) := by
  cases r <;> rfl

theorem mapWideArray_index {N : Usize} (g : Array V10Wide N) (i : Usize) :
    Aeneas.Std.Array.index_usize (mapWideArray g) i =
      mapResult wideToEbyK (Aeneas.Std.Array.index_usize g i) := by
  unfold mapWideArray
  simp only [Aeneas.Std.Array.index_usize,
    Aeneas.Std.Array.getElem?_Usize_eq, List.getElem?_map]
  cases hr : g.val[i.val]? with
  | none => simp [mapResult, hr]
  | some y => simp [mapResult, hr]

def v10TermBody
  (ops : BodyOps)
  (q : Array Std.U8 608#usize)
  (g : Array V10Wide 29#usize) (slot : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (sums : Array Std.U64 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    8#usize)) (Array Std.U64 8#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sums)
  | some term =>
    let i ← slot * 120#usize
    let i1 ← term * 4#usize
    let i2 ← i + i1
    let i3 ← i + i1
    let i4 ← i3 + 4#usize
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
        { start := i2, «end» := i4 }
    let r ←
      core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
    let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
    let o1 ← ops.m31FromBytes a
    let scalar ← core.option.Option.unwrap o1
    let we ← Array.index_usize g term
    let coefficient ← ops.wideToLimbs we
    let i5 ← Array.index_usize coefficient 0#usize
    let i6 ← lift (core.convert.num.FromU64U32.from i5)
    let i7 ← lift (core.convert.num.FromU64U32.from scalar)
    let i8 ← i6 * i7
    let i9 ← Array.index_usize sums 0#usize
    let i10 ← i9 + i8
    let sums1 ← Array.update sums 0#usize i10
    let i11 ← Array.index_usize coefficient 1#usize
    let i12 ← lift (core.convert.num.FromU64U32.from i11)
    let i13 ← lift (core.convert.num.FromU64U32.from scalar)
    let i14 ← i12 * i13
    let i15 ← Array.index_usize sums1 1#usize
    let i16 ← i15 + i14
    let sums2 ← Array.update sums1 1#usize i16
    let i17 ← Array.index_usize coefficient 2#usize
    let i18 ← lift (core.convert.num.FromU64U32.from i17)
    let i19 ← lift (core.convert.num.FromU64U32.from scalar)
    let i20 ← i18 * i19
    let i21 ← Array.index_usize sums2 2#usize
    let i22 ← i21 + i20
    let sums3 ← Array.update sums2 2#usize i22
    let i23 ← Array.index_usize coefficient 3#usize
    let i24 ← lift (core.convert.num.FromU64U32.from i23)
    let i25 ← lift (core.convert.num.FromU64U32.from scalar)
    let i26 ← i24 * i25
    let i27 ← Array.index_usize sums3 3#usize
    let i28 ← i27 + i26
    let sums4 ← Array.update sums3 3#usize i28
    let i29 ← Array.index_usize coefficient 4#usize
    let i30 ← lift (core.convert.num.FromU64U32.from i29)
    let i31 ← lift (core.convert.num.FromU64U32.from scalar)
    let i32 ← i30 * i31
    let i33 ← Array.index_usize sums4 4#usize
    let i34 ← i33 + i32
    let sums5 ← Array.update sums4 4#usize i34
    let i35 ← Array.index_usize coefficient 5#usize
    let i36 ← lift (core.convert.num.FromU64U32.from i35)
    let i37 ← lift (core.convert.num.FromU64U32.from scalar)
    let i38 ← i36 * i37
    let i39 ← Array.index_usize sums5 5#usize
    let i40 ← i39 + i38
    let sums6 ← Array.update sums5 5#usize i40
    let i41 ← Array.index_usize coefficient 6#usize
    let i42 ← lift (core.convert.num.FromU64U32.from i41)
    let i43 ← lift (core.convert.num.FromU64U32.from scalar)
    let i44 ← i42 * i43
    let i45 ← Array.index_usize sums6 6#usize
    let i46 ← i45 + i44
    let sums7 ← Array.update sums6 6#usize i46
    let i47 ← Array.index_usize coefficient 7#usize
    let i48 ← lift (core.convert.num.FromU64U32.from i47)
    let i49 ← lift (core.convert.num.FromU64U32.from scalar)
    let i50 ← i48 * i49
    let i51 ← Array.index_usize sums7 7#usize
    let i52 ← i51 + i50
    let sums8 ← Array.update sums7 7#usize i52
    ok (cont (iter1, sums8))

theorem v10TermBody_eq_fixedBody
    (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize)
    (iter : core.ops.range.Range Usize) (sums : Array U64 8#usize) :
    v10TermBody (adaptOps ops) q g slot iter sums =
      AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0_loop0.body
        ops q (mapWideArray g) slot iter sums := by
  unfold v10TermBody AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0_loop0.body
  simp only [adaptOps, mapWideArray_index, bind_mapResult]
  rfl

#print axioms mapWideArray_index
#print axioms v10TermBody_eq_fixedBody

end AspisR1FastDotsV10TypedInnerBodyOpsV1
