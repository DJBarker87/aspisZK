import NMS_OwnedPackets
set_option autoImplicit false
namespace NMS_Continuation
open Aeneas Aeneas.Std AdapterRw NMS_OwnedPackets
/-- Normal returns have a post-world. Emitted fail/div and independent native
stops have only their prefix; no conversion invents a returned reply/world. -/
inductive Outcome (World Event Value Pending : Type) where
 | returned (reply : core.result.Result Value PE) (post : World) (events : List Event)
 | emittedAbort (cause : Stop) (events : List Event)
 | stopped (events : List Event) (pending : Pending)

def prepend {W E A P : Type} (prefix : List E) : Outcome W E A P → Outcome W E A P
 | .returned reply post events => .returned reply post (prefix ++ events)
 | .emittedAbort cause events => .emittedAbort cause (prefix ++ events)
 | .stopped events pending => .stopped (prefix ++ events) pending

def bind {W E A B P : Type} : Outcome W E A P → (A → W → Outcome W E B P) → Outcome W E B P
 | .returned (.Ok value) post events, next => prepend events (next value post)
 | .returned (.Err error) post events, _ => .returned (.Err error) post events
 | .emittedAbort cause events, _ => .emittedAbort cause events
 | .stopped events pending, _ => .stopped events pending

def returnedValue {W E A P : Type} : Outcome W E A P → Option (core.result.Result A PE × W)
 | .returned reply post _ => some (reply,post)
 | .emittedAbort _ _ => none
 | .stopped _ _ => none

theorem prepend_assoc {W E A P : Type} (a b : List E) (outcome : Outcome W E A P) :
 prepend a (prepend b outcome) = prepend (a ++ b) outcome := by
 cases outcome <;> simp only [prepend,List.append_assoc]

theorem bind_prepend {W E A B P : Type} (prefix : List E) (outcome : Outcome W E A P)
 (next : A → W → Outcome W E B P) :
 bind (prepend prefix outcome) next = prepend prefix (bind outcome next) := by
 cases outcome with
 | returned reply post events => cases reply <;> simp only [prepend,bind,prepend_assoc]
 | emittedAbort _ _ => rfl
 | stopped _ _ => rfl

theorem bind_assoc {W E A B C P : Type} (outcome : Outcome W E A P)
 (next : A → W → Outcome W E B P) (last : B → W → Outcome W E C P) :
 bind (bind outcome next) last = bind outcome (fun a w => bind (next a w) last) := by
 cases outcome with
 | returned reply post events =>
  cases reply with
  | Ok _ => exact bind_prepend _ _ _
  | Err _ => rfl
 | emittedAbort _ _ => rfl
 | stopped _ _ => rfl

theorem stopped_prefix {W E A B P : Type} (events : List E) (pending : P)
 (next : A → W → Outcome W E B P) :
 bind (.stopped events pending : Outcome W E A P) next = .stopped events pending := rfl

theorem stopped_has_no_return {W E A P : Type} (events : List E) (pending : P) :
 returnedValue (.stopped events pending : Outcome W E A P) = none := rfl

theorem error_payload {W E A B P : Type} (error : PE) (post : W) (events : List E)
 (next : A → W → Outcome W E B P) :
 bind (.returned (.Err error) post events : Outcome W E A P) next =
 .returned (.Err error) post events := rfl
#print axioms prepend_assoc
#print axioms bind_prepend
#print axioms bind_assoc
#print axioms stopped_prefix
#print axioms stopped_has_no_return
#print axioms error_payload
end NMS_Continuation
