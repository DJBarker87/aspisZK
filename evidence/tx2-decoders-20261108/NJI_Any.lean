import NJI_Extracted.Master
set_option autoImplicit false
namespace NJI_Any
open Aeneas Aeneas.Std Result

/-- Source-ordered one-step reference for Iter::any; callback state is threaded.
No suffix is evaluated after a true callback, failure or divergence. -/
def run {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (xs : List T) (f : F) : Result (Bool × Nat × F) :=
 match xs with
 | [] => ok (false,0,f)
 | x::rest =>
   match cmp.call_mut f x with
   | .fail e => .fail e
   | .div => .div
   | .ok (hit,f') =>
     if hit then ok (true,1,f')
     else
       match run cmp rest f' with
       | .fail e => .fail e
       | .div => .div
       | .ok (answer,n,f'') => ok (answer,n+1,f'')
termination_by xs.length

def any {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (it : core.slice.iter.Iter T) (f : F) : Result (Bool × core.slice.iter.Iter T) := do
 let (b,n,_) ← run cmp (it.slice.val.drop it.i) f
 ok (b,{it with i:=it.i+n})

theorem pure_run {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (predicate : T → Bool)
 (law : ∀ f x, cmp.call_mut f x=ok (predicate x,f))
 (xs : List T) (f : F) :
 ∃ n, n≤xs.length ∧ run cmp xs f=ok (xs.any predicate,n,f) := by
 induction xs generalizing f with
 | nil => exact ⟨0,by simp,by simp [run]⟩
 | cons x xs ih =>
  obtain ⟨n,bound,h⟩:=ih f
  by_cases hx : predicate x=true
  · refine ⟨1,by simp,?_⟩
    simp only [run,law,bind_tc_ok,hx,ite_true,List.any_cons,Bool.true_or]
  · have hx' : predicate x=false := Bool.eq_false_iff.mpr hx
    refine ⟨n+1,by simpa using Nat.add_le_add_right bound 1,?_⟩
    simp only [run,law,bind_tc_ok,hx',Bool.false_eq_true,ite_false,h,
      List.any_cons,Bool.false_or]

/-- The caller discards only the local iterator. All callback returns and
short-circuit order are still present in run; the pure callback law is discharged
at each actual emitted closure, never retained by a parent root. -/
theorem value {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (predicate : T → Bool)
 (law : ∀ f x, cmp.call_mut f x=ok (predicate x,f))
 (it : core.slice.iter.Iter T) (f : F) :
 (do let (b,_) ← any cmp it f;ok b)=ok ((it.slice.val.drop it.i).any predicate) := by
 obtain ⟨n,_,h⟩:=pure_run cmp predicate law (it.slice.val.drop it.i) f
 simp only [any,h,bind_tc_ok]
 rfl

theorem result {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (predicate : T → Bool)
 (law : ∀ f x, cmp.call_mut f x=ok (predicate x,f))
 (it : core.slice.iter.Iter T) (f : F) :
 ∃ itOut, any cmp it f=ok ((it.slice.val.drop it.i).any predicate,itOut) := by
 obtain ⟨n,_,h⟩:=pure_run cmp predicate law (it.slice.val.drop it.i) f
 exact ⟨{it with i:=it.i+n},by simp only [any,h,bind_tc_ok];rfl⟩

#print axioms pure_run
#print axioms value
#print axioms result
end NJI_Any
