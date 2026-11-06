import NJJ_Common
set_option autoImplicit false
namespace NJU_Log
open Aeneas Aeneas.Std

/-- The log survives the first fail/div. Inner Rust Err branches are handled
by the frozen caller's own Try residual code. No independent log is supplied. -/
structure Run (E A : Type) where
 result : Result A
 events : List E

def bind {E A B : Type} (m : Run E A) (k : A → Run E B) : Run E B :=
 match m.result with
 | .fail err => ⟨.fail err,m.events⟩
 | .div => ⟨.div,m.events⟩
 | .ok a => let next:=k a; ⟨next.result,m.events++next.events⟩

instance {E : Type} : Monad (Run E) where
 pure a := ⟨.ok a,[]⟩
 bind := bind

instance {E : Type} : MonadLift Result (Run E) where
 monadLift call := ⟨call,[]⟩

def record {E A : Type} (event : Result A → E) (call : Result A) : Run E A :=
 ⟨call,[event call]⟩

theorem erase_bind {E A B : Type} (m : Run E A) (k : A → Run E B) :
 (m >>= k).result=(m.result >>= fun a=>(k a).result) := by
 cases m with
 | mk result events => cases result <;> rfl

theorem erase_pure {E A : Type} (a : A) :
 (pure a : Run E A).result=Result.ok a := rfl

theorem erase_lift {E A : Type} (call : Result A) :
 (monadLift call : Run E A).result=call := rfl

theorem erase_liftM {E A : Type} (call : Result A) :
 (liftM call : Run E A).result=call := rfl

theorem erase_record {E A : Type} (event : Result A → E) (call : Result A) :
 (record event call).result=call := rfl

theorem erase_if {E A : Type} (p : Prop) [Decidable p] (a b : Run E A) :
 (if p then a else b).result=if p then a.result else b.result := by
 split <;> rfl

theorem erase_flow {E A B C : Type} (flow : core.ops.control_flow.ControlFlow C B)
 (yes : B → Run E A) (no : C → Run E A) :
 (match flow with | .Continue x=>yes x | .Break x=>no x).result=
 match flow with | .Continue x=>(yes x).result | .Break x=>(no x).result := by
 cases flow <;> rfl

theorem prod_cases {A B C : Type} (p : A × B) (f : A → B → C) :
 (match p with | (a,b)=>f a b)=f p.1 p.2 := by
 cases p; rfl

theorem fail_prefix {E A B : Type} (m : Run E A) (err : Error)
 (failed : m.result=.fail err) (k : A → Run E B) :
 (m >>= k).result=.fail err ∧ (m >>= k).events=m.events := by
 change (bind m k).result=_ ∧ (bind m k).events=_
 simp only [bind,failed]
 exact ⟨True.intro,True.intro⟩

theorem div_prefix {E A B : Type} (m : Run E A)
 (failed : m.result=.div) (k : A → Run E B) :
 (m >>= k).result=.div ∧ (m >>= k).events=m.events := by
 change (bind m k).result=_ ∧ (bind m k).events=_
 simp only [bind,failed]
 exact ⟨True.intro,True.intro⟩

#print axioms erase_bind
#print axioms erase_pure
#print axioms erase_lift
#print axioms erase_liftM
#print axioms erase_record
#print axioms erase_if
#print axioms erase_flow
#print axioms prod_cases
#print axioms fail_prefix
#print axioms div_prefix
end NJU_Log
