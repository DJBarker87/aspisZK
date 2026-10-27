import R1Z.PV_CB_ForwardLoop
set_option autoImplicit false
namespace R1Z.PV_CB_PartialForward
open Aeneas Aeneas.Std Result PV_CB_ForwardRange

def Post {A : Type} (valid : A → Prop) (run : Result A) : Prop :=
  ∀ value, run = ok value → valid value

theorem bind {A B : Type} (valid : B → Prop) (run : Result A) (next : A → Result B)
    (preserve : ∀ input, run = ok input → Post valid (next input)) :
    Post valid (do let input ← run; next input) := by
  cases run with
  | ok input => exact preserve input rfl
  | fail err => intro out h; cases h
  | div => intro out h; cases h

theorem finite {A : Type} (valid : A → Prop) (step : Usize → A → Result A)
    (preserve : ∀ i state, valid state → Post valid (step i state))
    (fuel : Nat) (i : Usize) (state : A) (vs : valid state) :
    Post valid (PV_CB_ForwardLoop.finite step fuel i state) := by
  induction fuel generalizing i state with
  | zero => intro out h; cases h; exact vs
  | succ fuel ih =>
    unfold PV_CB_ForwardLoop.finite
    apply bind
    intro next hr
    exact ih (advance i) next (preserve i state vs next hr)
#print axioms bind
#print axioms finite
end R1Z.PV_CB_PartialForward
