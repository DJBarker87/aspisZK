import XSe_ListDriver
import XRo_Join_ResultTransport
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XSe_EnumeratedDriver

def step {I S E : Type} (next : S → Result S)
 (stage : S → I → Result (core.result.Result Unit E))
 (item : I) (s : S) : Result (core.result.Result S E) := do
 let s' ← next s
 let status ← stage s item
 match status with
 | .Err e => ok (.Err e)
 | .Ok _ => ok (.Ok s')

def body {I S E : Type} (next : S → Result S)
 (stage : S → I → Result (core.result.Result Unit E))
 (state : List I × S) : Result (ControlFlow (List I × S) (core.result.Result Unit E)) :=
 match state with
 | ([],_) => ok (.done (.Ok ()))
 | (item::rest,s) => do
   let s' ← next s
   let status ← stage s item
   match status with
   | .Err e => ok (.done (.Err e))
   | .Ok _ => ok (.cont (rest,s'))

def finish {S E : Type} (s : core.result.Result S E) : core.result.Result Unit E :=
 match s with | .Err e => .Err e | .Ok _ => .Ok ()
/-- Generic enumerated first-stop loop, including a failing checked successor.
All state and error transport occurs in the parametric fold. -/
theorem source {I S E : Type} (next : S → Result S)
 (stage : S → I → Result (core.result.Result Unit E)) (items : List I) (s : S) :
 loop (body next stage) (items,s)=
 XRo_Join_Carriers.mapR finish (XSe_ListDriver.fold (step next stage) items (.Ok s)) := by
 induction items generalizing s with
 | nil => rw [loop]; rfl
 | cons item rest ih =>
   rw [loop]
   simp only [body,XSe_ListDriver.fold,step,XRo_Join_Carriers.mapR_bind]
   cases hn : next s with
   | fail e => rfl
   | div => rfl
   | ok s' =>
     simp only [hn,bind_tc_ok]
     cases hs : stage s item with
     | fail e => rfl
     | div => rfl
     | ok status =>
       simp only [hs,bind_tc_ok]
       cases status with
       | Err e => cases rest <;> rfl
       | Ok u => exact ih s'
#print axioms source
end XSe_EnumeratedDriver
