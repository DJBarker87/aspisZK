import R1Z.PV_CB_ProducerPost
set_option autoImplicit false
namespace R1Z.PV_CB_ProducerBind
open Aeneas Aeneas.Std Result PV_CB_ProducerPost

theorem bind {A B E : Type} (valid : B → Prop) (run : Result A)
    (next : A → Result (core.result.Result B E))
    (post : ∀ input, run = ok input → Good valid (next input)) :
    Good valid (do let input ← run; next input) := by
  cases run with
  | ok input => exact post input rfl
  | fail err => intro value eq; cases eq
  | div => intro value eq; cases eq

theorem inner {A B E : Type} (va : A → Prop) (vb : B → Prop)
    (run : core.result.Result A E) (next : A → Result (core.result.Result B E))
    (post : ∀ input, run = .Ok input → va input)
    (step : ∀ input, va input → Good vb (next input)) :
    Good vb (match run with | .Ok input => next input | .Err err => ok (.Err err)) := by
  cases run with
  | Ok input => exact step input (post input rfl)
  | Err err => exact PV_CB_ProducerPost.error vb err
#print axioms bind
#print axioms inner
end R1Z.PV_CB_ProducerBind
