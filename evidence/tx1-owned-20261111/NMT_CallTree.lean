import Aeneas
set_option autoImplicit false
namespace AspisR1.NMT_CallTree
open Aeneas Aeneas.Std Result
/-- Full typed call arguments AND complete reply, at the actual entered site. -/
inductive Event : Type 1 where
 | call {Args Reply : Type} (site : String) (args : Args) (reply : Result Reply)
inductive Code (A : Type) : Type 1 where
 | done (a : A)
 | plain {B : Type} (reply : Result B) (next : B → Code A)
 | call {Args B : Type} (site : String) (args : Args) (reply : Result B) (next : B → Code A)
def bind {A B : Type} : Code A → (A → Code B) → Code B
 | .done a,k => k a
 | .plain r c,k => .plain r (fun b => bind (c b) k)
 | .call s a r c,k => .call s a r (fun b => bind (c b) k)
instance : Monad Code where
 pure := Code.done
 bind := bind
instance : MonadLift Result Code where
 monadLift r := .plain r .done
def invoke {Args A : Type} (site : String) (args : Args) (reply : Result A) : Code A :=
 .call site args reply .done
def erase {A : Type} : Code A → Result A
 | .done a => .ok a
 | .plain r k => do let x ← r; erase (k x)
 | .call _ _ r k => do let x ← r; erase (k x)
def run {A : Type} : Code A → Result A × List Event
 | .done a => (.ok a,[])
 | .plain r k => match r with
   | .ok x => run (k x)
   | .fail e => (.fail e,[])
   | .div => (.div,[])
 | .call s a r k => match r with
   | .ok x => let out:=run (k x); (out.1,Event.call s a r::out.2)
   | .fail e => (.fail e,[Event.call s a r])
   | .div => (.div,[Event.call s a r])
@[simp] theorem result_right {A : Type} (r : Result A) :
 Aeneas.Std.bind r (fun a => .ok a)=r := by cases r <;> rfl
@[simp] theorem result_assoc {A B C : Type} (r : Result A) (f : A → Result B) (g : B → Result C) :
 Aeneas.Std.bind (Aeneas.Std.bind r f) g=Aeneas.Std.bind r (fun a => Aeneas.Std.bind (f a) g) := by cases r <;> rfl
#print axioms result_right
#print axioms result_assoc
theorem result_congr {A B : Type} (r : Result A) (f g : A → Result B)
 (same : ∀ a,f a=g a) : Aeneas.Std.bind r f=Aeneas.Std.bind r g := by
 cases r with
 | ok a => exact same a
 | fail e => rfl
 | div => rfl
#print axioms result_congr
theorem erase_bind {A B : Type} (c : Code A) (k : A → Code B) :
 erase (bind c k) = (erase c >>= fun a => erase (k a)) := by
 induction c with
 | done a => rfl
 | plain r c ih => cases r <;> simp only [bind,erase,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]
 | call s a r c ih => cases r <;> simp only [bind,erase,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]
theorem erase_invoke {Args A : Type} (site : String) (args : Args) (reply : Result A) :
 erase (invoke site args reply)=reply := by cases reply <;> rfl
theorem erase_lift {A : Type} (r : Result A) : erase (monadLift r : Code A)=r := by cases r <;> rfl
theorem erase_pure {A : Type} (a : A) : erase (pure a : Code A)=.ok a := rfl
theorem run_result {A : Type} (c : Code A) : (run c).1=erase c := by
 induction c with
 | done a => rfl
 | plain r c ih => cases r <;> simp only [run,erase,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]
 | call s a r c ih => cases r <;> simp only [run,erase,bind_tc_ok,bind_tc_fail,bind_tc_div,ih]
theorem stopped_prefix {Args A B : Type} (site : String) (args : Args) (e : Error) (k : A → Code B) :
 run (.call site args (.fail e) k)=(.fail e,[Event.call site args (.fail e : Result A)]) := rfl
#print axioms erase_bind
#print axioms erase_invoke
#print axioms erase_lift
#print axioms erase_pure
#print axioms run_result
#print axioms stopped_prefix
end AspisR1.NMT_CallTree
