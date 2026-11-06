import NJI_Any
set_option autoImplicit false
namespace NJQ_Library
open Aeneas Aeneas.Std Result
/-- Reuse NJI's callback-state-threading model rather than duplicate its proof. -/
abbrev any := @NJI_Any.any
abbrev run := @NJI_Any.run

theorem empty {T F : Type} (cmp : core.ops.function.FnMut F T Bool) (f : F) :
 run cmp [] f=ok (false,0,f) := rfl

theorem stop_true {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (x : T) (xs : List T) (f f' : F) (call : cmp.call_mut f x=ok (true,f')) :
 run cmp (x::xs) f=ok (true,1,f') := by simp [run,NJI_Any.run,call]

theorem stop_fail {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (x : T) (xs : List T) (f : F) (e : Aeneas.Error)
 (call : cmp.call_mut f x=.fail e) : run cmp (x::xs) f=.fail e := by
 simp [run,NJI_Any.run,call]

theorem stop_div {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (x : T) (xs : List T) (f : F) (call : cmp.call_mut f x=.div) :
 run cmp (x::xs) f=.div := by simp [run,NJI_Any.run,call]

/-- Full returning value for pure callbacks; no parent may assume this callback law.
The parent must discharge it on its exact emitted/transcribed closure. -/
theorem pure_value {T F : Type} (cmp : core.ops.function.FnMut F T Bool)
 (predicate : T → Bool) (law : ∀ f x,cmp.call_mut f x=ok (predicate x,f))
 (it : core.slice.iter.Iter T) (f : F) :
 (do let (b,_) ← any cmp it f;ok b)=ok ((it.slice.val.drop it.i).any predicate) :=
 NJI_Any.value cmp predicate law it f

#print axioms empty
#print axioms stop_true
#print axioms stop_fail
#print axioms stop_div
#print axioms pure_value
end NJQ_Library
