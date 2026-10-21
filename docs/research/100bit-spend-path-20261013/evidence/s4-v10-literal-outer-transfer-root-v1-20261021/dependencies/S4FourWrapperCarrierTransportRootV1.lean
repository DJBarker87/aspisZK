import S4V10TailMapRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S4FourWrapperCarrierTransportRootV1
open AspisR1FastDotsV10TailMapRootV1 (mapRes)

def mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩

def fourWrapper {E : Type}
    (one : Array U8 608#usize → Array E 29#usize → Usize → Result E)
    (q : Slice U8) (g : Array E 29#usize) : Result (Array E 4#usize) := do
  let s ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeToUsizeSlice U8) q {«end»:=608#usize}
  let r ← core.array.TryFromSharedArraySlice.try_from 608#usize s
  let prefixQ ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  let v0 ← one prefixQ g 0#usize
  let v1 ← one prefixQ g 1#usize
  let v2 ← one prefixQ g 2#usize
  let v3 ← one prefixQ g 3#usize
  .ok (Array.make 4#usize [v0,v1,v2,v3])

private theorem mapRes_bind {A B C : Type} (f : B → C) (r : Result A) (k : A → Result B) :
    mapRes f (r >>= k) = (r >>= fun x => mapRes f (k x)) := by cases r <;> rfl
private theorem bind_mapRes {A B C : Type} (f : A → B) (r : Result A) (k : B → Result C) :
    (mapRes f r >>= k) = (r >>= fun x => k (f x)) := by cases r <;> rfl
private theorem bind_congr_right {A B : Type} (r : Result A)
    (f g : A → Result B) (h : ∀ x, f x=g x) : (r >>= f)=(r >>= g) := by
  cases r with
  | ok x => exact h x
  | fail e => rfl
  | div => rfl

/-- Exact four-call wrapper transport, preserving every prefix rejection and
helper Result outcome. The complete helper theorem supplies hOne. -/
theorem four_wrapper_map_all {A B : Type} (f : A → B)
    (oneA : Array U8 608#usize → Array A 29#usize → Usize → Result A)
    (oneB : Array U8 608#usize → Array B 29#usize → Usize → Result B)
    (q : Slice U8) (g : Array A 29#usize)
    (hOne : ∀ prefixQ slot,
      oneB prefixQ (mapArray f g) slot = mapRes f (oneA prefixQ g slot)) :
    mapRes (mapArray f) (fourWrapper oneA q g) =
      fourWrapper oneB q (mapArray f g) := by
  unfold fourWrapper
  simp only [hOne,mapRes_bind,bind_mapRes]
  repeat' (apply bind_congr_right; intro x)
  rfl

/-- This generic wrapper is exactly the retained fixed-v6 outer body. -/
theorem current_outer_eq_wrapper (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (q : Slice U8)
    (g : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 29#usize) :
    AspisR1FastDotsCurrent.fast_dots.four_dots_fixed ops q g =
      fourWrapper (AspisR1FastDotsCurrent.fast_dots.four_dots_one ops) q g := rfl

/-- Field-array transport is reversible under the actual pointwise inverse. -/
theorem mapArray_inverse {A B : Type} {N : Usize} (f : A → B) (g : B → A)
    (hinv : ∀ a, g (f a) = a) (a : Array A N) :
    mapArray g (mapArray f a) = a := by
  cases a with
  | mk xs h =>
    apply Subtype.ext
    simp only [mapArray, List.map_map]
    change xs.map (fun x => g (f x)) = xs
    exact List.map_id'' hinv xs

#print axioms four_wrapper_map_all
#print axioms current_outer_eq_wrapper
#print axioms mapArray_inverse
end AspisR1S4FourWrapperCarrierTransportRootV1
