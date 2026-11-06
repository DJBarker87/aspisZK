import S2StdAnySourceTotalV1
import NJI_Any
set_option autoImplicit false
namespace NJI_StdAnyTransport
open Aeneas Aeneas.Std Result ControlFlow AspisS2StdAnySource

-- Numeric private-name components are Name.num, not quoted string components.
-- Reuse the exact canonical private theorem discovered in NJI_L041.
open Lean in
macro "nji_std_any_unfold" : tactic => do
 let n := Name.str (Name.str (Name.num
   (Name.str (Name.str Name.anonymous "_private") "S2StdAnySourceTotalV1") 0)
   "AspisS2StdAnySource") "anyLoop_unfold"
 let id := mkIdent n
 `(tactic| rw [($id:ident)])

def next {T : Type} (it : SourceIter (List T) Unit) :
 Result (Option T × SourceIter (List T) Unit) :=
 match it.ptr with
 | [] => ok (none,it)
 | x::xs => ok (some x,{it with ptr:=xs})

/-- Reuse the canonical emitted std loop and its private, generic unfolding law.
This extends the already CLOSED byte/nonzero theorem to the U64 capacity callback;
the concrete callback law is discharged at the parent's emitted closure. -/
theorem loop_pure {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (predicate : T → Bool) (law : ∀ f x, cmp.call_mut f x=ok (predicate x,f))
 (xs : List T) (f : F) :
 ∃ rest, anyLoop next cmp xs () f=
  ok (rest,(),if xs.any predicate then some true else none) := by
 induction xs generalizing f with
 | nil =>
  refine ⟨[],?_⟩
  nji_std_any_unfold
  simp only [anyBody,next,bind_tc_ok,List.any_nil,Bool.false_eq_true,ite_false]
  rfl
 | cons x xs ih =>
  cases hx : predicate x with
  | true =>
   refine ⟨xs,?_⟩
   nji_std_any_unfold
   simp [anyBody,next,law,hx]
  | false =>
   obtain ⟨rest,h⟩:=ih f
   refine ⟨rest,?_⟩
   nji_std_any_unfold
   simpa [anyBody,next,law,hx] using h

theorem source_pure {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (predicate : T → Bool) (law : ∀ f x, cmp.call_mut f x=ok (predicate x,f))
 (xs : List T) (f : F) :
 ∃ itOut, sourceAny next cmp {ptr:=xs,end_or_len:=(),_marker:=()} f=
  ok (xs.any predicate,itOut) := by
 obtain ⟨rest,h⟩:=loop_pure cmp predicate law xs f
 refine ⟨{ptr:=rest,end_or_len:=(),_marker:=()},?_⟩
 unfold sourceAny
 rw [h,bind_tc_ok]
 cases hx : xs.any predicate <;> rfl

/-- Native one-step/same-slice association composes with this symbolic induction.
The parent's local iterator is discarded only after its complete source loop. -/
theorem association {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (predicate : T → Bool) (law : ∀ f x, cmp.call_mut f x=ok (predicate x,f))
 (it : core.slice.iter.Iter T) (f : F) :
 (do let (answer,_) ← sourceAny next cmp
      {ptr:=it.slice.val.drop it.i,end_or_len:=(),_marker:=()} f;ok answer)=
 (do let (answer,_) ← NJI_Any.any cmp it f;ok answer) := by
 obtain ⟨itOut,h⟩:=source_pure cmp predicate law (it.slice.val.drop it.i) f
 rw [h,bind_tc_ok,NJI_Any.value cmp predicate law]

#print axioms loop_pure
#print axioms source_pure
#print axioms association
end NJI_StdAnyTransport
