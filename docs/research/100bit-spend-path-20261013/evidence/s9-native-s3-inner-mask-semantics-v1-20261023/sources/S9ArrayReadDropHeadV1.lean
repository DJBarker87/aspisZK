import Aeneas.Std
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ArrayReadDropHeadV1

theorem array_read_option {A : Type} {N : Usize} (a : Array A N) (i : Usize) (x : A)
    (h : Array.index_usize a i=.ok x) : a.val[i.val]?=some x := by
  unfold Array.index_usize at h
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some value => Result.ok value)=Result.ok x at h
  cases hi : a.val[i.val]? with
  | none => simp only [hi] at h;cases h
  | some value =>
    simp only [hi] at h
    have he : value=x := Result.ok.inj h
    subst value
    rfl

/-- Converts a SAME accepted array read into the exact source-model decoded
head of its dropped list, without guessing an independent lookup value. -/
theorem array_read_map_drop_head {A B : Type} {N : Usize}
    (f : A → B) (fallback : B) (a : Array A N) (i : Usize) (x : A)
    (h : Array.index_usize a i=.ok x) :
    ((a.val.map f).drop i.val).headD fallback=f x := by
  have hi := array_read_option a i x h
  rw [←List.map_drop,List.drop_eq_getElem?_toList_append,hi] <;> rfl

#print axioms array_read_option
#print axioms array_read_map_drop_head
end AspisR1S9ArrayReadDropHeadV1
