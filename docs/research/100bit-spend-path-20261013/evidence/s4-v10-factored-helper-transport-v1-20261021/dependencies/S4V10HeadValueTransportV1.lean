import S4V10HeadLoopBoundV1
import AspisR1FastDotsCurrent.FunsOpsFixedV6

open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisR1FastDotsV10HeadValueTransportV1
open AspisR1FastDotsV10CarrierMapV1
open AspisR1FastDotsV10HeadLoopBoundV1
open AspisR1FastDotsV10TypedInnerBodyOpsV1
abbrev CurrentOps := AspisR1FastDotsCurrent.FourDotsOps
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Usize := Aeneas.Std.Usize
abbrev U64 := Aeneas.Std.U64
abbrev U32 := Aeneas.Std.U32

def mapRes {A B : Type} (f : A → B) : Result A → Result B
| .ok x => .ok (f x)
| .fail e => .fail e
| .div => .div

private theorem mapRes_bind {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) : mapRes f (r >>= k) = r >>= fun x => mapRes f (k x) := by
  cases r <;> rfl

private theorem bind_congr_right {A B : Type} (r : Result A)
    (f g : A → Result B) (h : ∀ x, f x = g x) : (r >>= f) = (r >>= g) := by
  cases r with
  | ok x => exact h x
  | fail e => rfl
  | div => rfl

theorem bind_map_inverse {A B : Type} (f : B → A) (g : A → B)
    (hinv : ∀ b, g (f b) = b) (left : Result A) (right : Result B)
    (hprefix : left = mapRes f right) (k : A → Result A) (l : B → Result B)
    (hstep : ∀ a, k a = mapRes f (l (g a))) :
    left >>= k = mapRes f (right >>= l) := by
  cases right with
  | ok b =>
    have hleft : left = .ok (f b) := by simpa [mapRes] using hprefix
    rw [hleft]
    simp only [bind_tc_ok]
    rw [hstep (f b), hinv b]
  | fail e =>
    have hleft : left = .fail e := by simpa [mapRes] using hprefix
    rw [hleft]
    rfl
  | div =>
    have hleft : left = .div := by simpa [mapRes] using hprefix
    rw [hleft]
    rfl

private theorem v10HeadLoop_all_result (ops : CurrentOps) (iter : StepBy)
    (q : Array Std.U8 608#usize) (g : Array V10Wide 29#usize)
    (slot : Usize) (limbs : Array U64 8#usize) :
    v10HeadLoop ops iter q g slot limbs =
      AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0 ops iter q (mapWideArray g) slot limbs := by
  change Aeneas.Std.loop
      (fun st : StepBy × Array U64 8#usize => v10HeadBody ops q g slot st.1 st.2) (iter, limbs) =
    Aeneas.Std.loop
      (fun st : StepBy × Array U64 8#usize => CurrentBody ops q (mapWideArray g) slot st.1 st.2)
      (iter, limbs)
  apply congrArg (fun body => Aeneas.Std.loop body (iter,limbs))
  funext st
  exact v10HeadBody_eq_fixedBody ops q g slot st.1 st.2

/-- The literal eight `reduce_u64` calls in the V10 parent, factored once so
    both sides of the carrier transport share exactly the same ordered sequence. -/
def reduceHeadLimbs (ops : CurrentOps) (limbs : Array U64 8#usize) : Result (Array U32 8#usize) := do
  let i ← Array.index_usize limbs 0#usize
  let m ← ops.m31ReduceU64 i
  let i1 ← Array.index_usize limbs 1#usize
  let m1 ← ops.m31ReduceU64 i1
  let i2 ← Array.index_usize limbs 2#usize
  let m2 ← ops.m31ReduceU64 i2
  let i3 ← Array.index_usize limbs 3#usize
  let m3 ← ops.m31ReduceU64 i3
  let i4 ← Array.index_usize limbs 4#usize
  let m4 ← ops.m31ReduceU64 i4
  let i5 ← Array.index_usize limbs 5#usize
  let m5 ← ops.m31ReduceU64 i5
  let i6 ← Array.index_usize limbs 6#usize
  let m6 ← ops.m31ReduceU64 i6
  let i7 ← Array.index_usize limbs 7#usize
  let m7 ← ops.m31ReduceU64 i7
  ok (Array.make 8#usize [m,m1,m2,m3,m4,m5,m6,m7])

def v10HeadPack (ops : CurrentOps) (reduced : Array U32 8#usize) : Result V10Wide := do
  let o ← ops.wideFromLimbs reduced
  core.option.Option.unwrap (Option.map wideFromEbyK o)

def fixedHeadPack (ops : CurrentOps) (reduced : Array U32 8#usize) : Result Wide := do
  let o ← ops.wideFromLimbs reduced
  core.option.Option.unwrap o

theorem head_pack_eq_fixed (ops : CurrentOps) (reduced : Array U32 8#usize) :
    v10HeadPack ops reduced = mapRes wideFromEbyK (fixedHeadPack ops reduced) := by
  unfold v10HeadPack fixedHeadPack mapRes
  cases h : ops.wideFromLimbs reduced with
  | ok o => cases o <;> rfl
  | fail e => rfl
  | div => rfl

def v10HeadValue (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) : Result V10Wide := do
  let limbs := Array.repeat 8#usize 0#u64
  let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := 26#usize } 4#usize
  let limbs1 ← v10HeadLoop ops iter q g slot limbs
  let reduced ← reduceHeadLimbs ops limbs1
  v10HeadPack ops reduced

def fixedHeadValue (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) : Result Wide := do
  let limbs := Array.repeat 8#usize 0#u64
  let iter ← core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := 26#usize } 4#usize
  let limbs1 ← AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0 ops iter q (mapWideArray g) slot limbs
  let reduced ← reduceHeadLimbs ops limbs1
  fixedHeadPack ops reduced

theorem head_value_eq_fixed (ops : CurrentOps) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) :
    v10HeadValue ops q g slot = mapRes wideFromEbyK (fixedHeadValue ops q g slot) := by
  unfold v10HeadValue fixedHeadValue
  simp only [v10HeadLoop_all_result, mapRes_bind]
  apply bind_congr_right
  intro iter
  apply bind_congr_right
  intro limbs1
  apply bind_congr_right
  intro reduced
  exact head_pack_eq_fixed ops reduced

#print axioms head_value_eq_fixed
end AspisR1FastDotsV10HeadValueTransportV1
