import NIV_RawBoundary
set_option autoImplicit false
namespace NJD_Trace
open Aeneas Aeneas.Std Result

/-- An aborting primitive remains in the chronological prefix. Result.fail/div
stop the continuation, without silently erasing earlier entered calls. -/
abbrev Run (Event Value : Type) := List Event × Result Value

def pure {Event Value : Type} (v : Value) : Run Event Value := ([],.ok v)
def call {Event Value : Type} (event : Event) (reply : Result Value) : Run Event Value :=
  ([event],reply)
def bind {Event A B : Type} (r : Run Event A) (next : A → Run Event B) : Run Event B :=
  match r.2 with
  | .ok a => let n := next a; (r.1 ++ n.1,n.2)
  | .fail e => (r.1,.fail e)
  | .div => (r.1,.div)

theorem erase_bind {Event A B : Type} (r : Run Event A) (next : A → Run Event B) :
    (bind r next).2 = (r.2 >>= fun a => (next a).2) := by
  cases r with | mk events result => cases result <;> rfl

theorem entered {Event Value : Type} (event : Event) (reply : Result Value) :
    (call event reply).1 = [event] := rfl

theorem fail_no_suffix {Event A B : Type} (events : List Event) (e : Error)
    (next : A → Run Event B) : bind (events,.fail e) next = (events,.fail e) := rfl

theorem div_no_suffix {Event A B : Type} (events : List Event)
    (next : A → Run Event B) : bind (events,.div) next = (events,.div) := rfl

theorem successful_prefix {Event A B : Type} (events : List Event) (a : A)
    (next : A → Run Event B) :
    (bind (events,.ok a) next).1 = events ++ (next a).1 := rfl

/-- Same-call post becomes next-call pre. No clause supplies an independently
chosen child output or a parent success equation. -/
theorem bind_assoc {Event A B C : Type} (r : Run Event A)
    (f : A → Run Event B) (g : B → Run Event C) :
    bind (bind r f) g = bind r (fun a => bind (f a) g) := by
  cases r with
  | mk events result =>
    cases result with
    | fail e => rfl
    | div => rfl
    | ok a =>
      cases hf : f a with
      | mk es v => cases v <;> simp only [bind,hf,List.append_assoc]

#print axioms erase_bind
#print axioms entered
#print axioms fail_no_suffix
#print axioms div_no_suffix
#print axioms successful_prefix
#print axioms bind_assoc
end NJD_Trace
