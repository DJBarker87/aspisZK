import Hiq_DispatchSource
set_option autoImplicit false
noncomputable section
namespace NMW_Outcome
open Aeneas Aeneas.Std
abbrev Reply := core.result.Result Unit AspisR1.Hiq_DispatchSource.PE
inductive Stop where
 | failure (error : Error)
 | divergence
inductive Outcome (World Event : Type) where
 | returned (reply : Reply) (post : World) (events : List Event)
 | stopped (reason : Stop) (history : List Event)
def result {W E : Type} : Outcome W E → Result Reply
 | .returned r _ _ => .ok r
 | .stopped (.failure e) _ => .fail e
 | .stopped .divergence _ => .div
def events {W E : Type} : Outcome W E → List E
 | .returned _ _ es => es
 | .stopped _ es => es
/-- Prefixing never creates a post-state for a stopped child. -/
def prepend {W E : Type} (history : List E) : Outcome W E → Outcome W E
 | .returned r w es => .returned r w (history ++ es)
 | .stopped why es => .stopped why (history ++ es)
theorem prepend_result {W E : Type} (es : List E) (r : Outcome W E) :
 result (prepend es r) = result r := by
 cases r with
 | returned reply post history => rfl
 | stopped reason history => cases reason <;> rfl
theorem prepend_events {W E : Type} (es : List E) (r : Outcome W E) :
 events (prepend es r) = es ++ events r := by cases r <;> rfl
#print axioms prepend_result
#print axioms prepend_events
end NMW_Outcome
end
