import S4V10TypedTermLoopBoundV2
import V6OuterSevenBatchBoundV1
import Aeneas.Std.RangeIter

open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1FastDotsV10HeadLoopBoundV1

open AspisR1FastDotsV10TypedTermLoopBoundV1
open AspisR1FastDotsV10TypedInnerBodyOpsV1
abbrev CurrentOps := AspisR1FastDotsCurrent.FourDotsOps
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact
abbrev Usize := Aeneas.Std.Usize
abbrev U64 := Aeneas.Std.U64
abbrev Range := Aeneas.Std.core.ops.range.Range Usize
abbrev StepBy := Aeneas.Std.core.iter.adapters.step_by.StepBy Range
abbrev CurrentLoop := AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0
abbrev CurrentBody := AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0.body
def v10HeadBody
  (ops : CurrentOps)
  (q : Array Std.U8 608#usize)
  (g : Array V10Wide 29#usize) (slot : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (limbs : Array Std.U64 8#usize) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × (Array Std.U64 8#usize)) (Array Std.U64 8#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done limbs)
  | some start =>
    let sums := Array.repeat 8#usize 0#u64
    let i ← start + 4#usize
    let i1 ← core.cmp.min core.cmp.OrdUsize i 26#usize
    let sums1 ←
      v10TermLoop (adaptOps ops) { start, «end» := i1 } q g slot sums
    let i2 ← Array.index_usize sums1 0#usize
    let i3 ← lift (i2 &&& 2147483647#u64)
    let i4 ← i2 >>> 31#i32
    let i5 ← i3 + i4
    let i6 ← Array.index_usize limbs 0#usize
    let i7 ← i6 + i5
    let limbs1 ← Array.update limbs 0#usize i7
    let i8 ← Array.index_usize sums1 1#usize
    let i9 ← lift (i8 &&& 2147483647#u64)
    let i10 ← i8 >>> 31#i32
    let i11 ← i9 + i10
    let i12 ← Array.index_usize limbs1 1#usize
    let i13 ← i12 + i11
    let limbs2 ← Array.update limbs1 1#usize i13
    let i14 ← Array.index_usize sums1 2#usize
    let i15 ← lift (i14 &&& 2147483647#u64)
    let i16 ← i14 >>> 31#i32
    let i17 ← i15 + i16
    let i18 ← Array.index_usize limbs2 2#usize
    let i19 ← i18 + i17
    let limbs3 ← Array.update limbs2 2#usize i19
    let i20 ← Array.index_usize sums1 3#usize
    let i21 ← lift (i20 &&& 2147483647#u64)
    let i22 ← i20 >>> 31#i32
    let i23 ← i21 + i22
    let i24 ← Array.index_usize limbs3 3#usize
    let i25 ← i24 + i23
    let limbs4 ← Array.update limbs3 3#usize i25
    let i26 ← Array.index_usize sums1 4#usize
    let i27 ← lift (i26 &&& 2147483647#u64)
    let i28 ← i26 >>> 31#i32
    let i29 ← i27 + i28
    let i30 ← Array.index_usize limbs4 4#usize
    let i31 ← i30 + i29
    let limbs5 ← Array.update limbs4 4#usize i31
    let i32 ← Array.index_usize sums1 5#usize
    let i33 ← lift (i32 &&& 2147483647#u64)
    let i34 ← i32 >>> 31#i32
    let i35 ← i33 + i34
    let i36 ← Array.index_usize limbs5 5#usize
    let i37 ← i36 + i35
    let limbs6 ← Array.update limbs5 5#usize i37
    let i38 ← Array.index_usize sums1 6#usize
    let i39 ← lift (i38 &&& 2147483647#u64)
    let i40 ← i38 >>> 31#i32
    let i41 ← i39 + i40
    let i42 ← Array.index_usize limbs6 6#usize
    let i43 ← i42 + i41
    let limbs7 ← Array.update limbs6 6#usize i43
    let i44 ← Array.index_usize sums1 7#usize
    let i45 ← lift (i44 &&& 2147483647#u64)
    let i46 ← i44 >>> 31#i32
    let i47 ← i45 + i46
    let i48 ← Array.index_usize limbs7 7#usize
    let i49 ← i48 + i47
    let limbs8 ← Array.update limbs7 7#usize i49
    ok (cont (iter1, limbs8))


def v10HeadLoop (ops : CurrentOps) (iter : StepBy)
    (q : Array Aeneas.Std.U8 608#usize) (g : Array V10Wide 29#usize)
    (slot : Usize) (limbs : Array U64 8#usize) : Result (Array U64 8#usize) :=
  Aeneas.Std.loop
    (fun st : StepBy × Array U64 8#usize => v10HeadBody ops q g slot st.1 st.2)
    (iter, limbs)

theorem v10HeadBody_eq_fixedBody (ops : CurrentOps)
    (q : Array Aeneas.Std.U8 608#usize) (g : Array V10Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs : Array U64 8#usize) :
    v10HeadBody ops q g slot iter limbs = CurrentBody ops q (mapWideArray g) slot iter limbs := by
  unfold v10HeadBody CurrentBody
  simp only [v10TermLoop_eq_fixedLoopV2]
  rfl

theorem v10HeadLoop_eq_fixedLoop (ops : CurrentOps)
    (q : Array Aeneas.Std.U8 608#usize) (g : Array V10Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs out : Array U64 8#usize)
    (h : v10HeadLoop ops iter q g slot limbs = .ok out) :
    CurrentLoop ops iter q (mapWideArray g) slot limbs = .ok out := by
  have heq : v10HeadLoop ops iter q g slot limbs = CurrentLoop ops iter q (mapWideArray g) slot limbs := by
    change Aeneas.Std.loop
        (fun st : StepBy × Array U64 8#usize => v10HeadBody ops q g slot st.1 st.2) (iter, limbs) =
      Aeneas.Std.loop
        (fun st : StepBy × Array U64 8#usize => CurrentBody ops q (mapWideArray g) slot st.1 st.2) (iter, limbs)
    apply congrArg (fun body => Aeneas.Std.loop body (iter, limbs))
    funext st
    exact v10HeadBody_eq_fixedBody ops q g slot st.1 st.2
  exact heq.symm.trans h

theorem v10HeadLoop_success_seven_bound
    (ops : AspisR1FastDotsV6OuterSevenBatchBoundV1.Ops)
    (q : Array Aeneas.Std.U8 608#usize) (g : Array V10Wide 29#usize)
    (slot : Usize) (out : Array U64 8#usize)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        ((mapWideArray g).val[i.val]'(by simpa [mapWideArray, List.length_map] using i.isLt)))
    (hloop : v10HeadLoop
      (AspisR1FastDotsV6OuterLoopSuccessTransferV1.NewOps ops)
      AspisR1FastDotsStepSchedule.startBy q g slot
      (Array.repeat 8#usize 0#u64) = .ok out) :
    ∀ i : Fin 8,
      AspisR1FastDotsActualSevenBatchLimbBoundV2.cell out i ≤
        7 * AspisR1FastDotsActualSevenBatchLimbBoundV2.Cap := by
  have hfixed := v10HeadLoop_eq_fixedLoop
    (AspisR1FastDotsV6OuterLoopSuccessTransferV1.NewOps ops)
    q g slot AspisR1FastDotsStepSchedule.startBy
    (Array.repeat 8#usize 0#u64) out hloop
  exact AspisR1FastDotsV6OuterSevenBatchBoundV1.v6_outer_startBy_success_seven_bound
    ops q (mapWideArray g) slot out hcoords hfixed

#print axioms v10HeadBody_eq_fixedBody
#print axioms v10HeadLoop_eq_fixedLoop
#print axioms v10HeadLoop_success_seven_bound

end AspisR1FastDotsV10HeadLoopBoundV1
