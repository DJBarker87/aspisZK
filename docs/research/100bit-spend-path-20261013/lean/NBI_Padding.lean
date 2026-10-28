import Port4B_AnyFalse
import Port4B_PaddingWord

set_option autoImplicit false
namespace AspisR1.NBI_Padding
open Aeneas Aeneas.Std Result ControlFlow

/-- Source order scan, including the exact unvisited remainder on first true,
and retaining predicate failures. One native eight-byte iteration is K024. -/
def scan (predicate : core.ops.function.FnMut Unit (Slice U8) Bool)
    (remainder : Slice U8) : List (Slice U8) → Result (Bool × core.slice.iter.ChunksExact U8)
  | [] => ok (false,{chunks := [],remainder := remainder})
  | chunk::rest => do
      let (stop,_) ← predicate.call_mut () chunk
      if stop then ok (true,{chunks := rest,remainder := remainder})
      else scan predicate remainder rest

/-- Total induction over the actual installed iterator; no accepted-only
postcondition, final scan equation, or whole-buffer Kani execution is assumed. -/
theorem any_eq_scan (predicate : core.ops.function.FnMut Unit (Slice U8) Bool)
    (chunks : List (Slice U8)) (remainder : Slice U8) :
    Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorChunksExact U8)
      predicate {chunks := chunks,remainder := remainder} () = scan predicate remainder chunks := by
  induction chunks with
  | nil =>
    unfold Port3_BatchStd.anyDefault
    rw [Aeneas.Std.loop.eq_def,Port4B_AnyFalse.body_nil]
    rfl
  | cons chunk rest ih =>
    unfold Port3_BatchStd.anyDefault
    rw [Aeneas.Std.loop.eq_def,Port4B_AnyFalse.body_cons]
    unfold scan
    generalize call : predicate.call_mut () chunk = out
    cases out with
    | fail e => rfl
    | div => rfl
    | ok pair =>
      rcases pair with ⟨stop,state⟩
      cases state
      cases stop with
      | true => rfl
      | false => exact ih

/-- A native all-zero scan consumes every chunk; a nonzero word stops before
its suffix is examined. The first stop cannot be silently moved to the end. -/
theorem first_stop (predicate : core.ops.function.FnMut Unit (Slice U8) Bool)
    (front suffix : List (Slice U8)) (chunk remainder : Slice U8)
    (zero : ∀ c ∈ front, predicate.call_mut () c = ok (false,()))
    (nonzero : predicate.call_mut () chunk = ok (true,())) :
    scan predicate remainder (front ++ chunk::suffix) =
      ok (true,{chunks := suffix,remainder := remainder}) := by
  induction front with
  | nil => simp only [List.nil_append,scan,nonzero,bind_tc_ok,ite_true]; rfl
  | cons a rest ih =>
    rw [List.cons_append,scan,zero a (by simp)]
    simp only [bind_tc_ok,Bool.false_eq_true,ite_false]
    exact ih (fun c hc => zero c (by simp [hc]))

#print axioms any_eq_scan
#print axioms first_stop
end AspisR1.NBI_Padding
