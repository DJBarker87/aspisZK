import Aeneas
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S9LoopInvariantPropertyV1

/-- A loop preserves a state invariant at every successful continuation, and
its terminal output property follows from that invariant.  The measure
condition makes the recursive argument well-founded. -/
theorem loop_invariant_property {α β : Type}
    (step : α → Result (ControlFlow α β))
    (measure : α → Nat) (Invariant : α → Prop) (OutputProperty : β → Prop)
    (hdone : ∀ s out, Invariant s → step s = .ok (.done out) → OutputProperty out)
    (hcontinue : ∀ s s', Invariant s → step s = .ok (.cont s') → Invariant s')
    (hdecrease : ∀ s s', step s = .ok (.cont s') → measure s' < measure s)
    : ∀ state out, Invariant state → Aeneas.Std.loop step state = .ok out →
        OutputProperty out := by
  intro state out
  induction hm : measure state using Nat.strong_induction_on generalizing state out with
  | h n ih =>
      intro hinv hloop
      rw [Aeneas.Std.loop.eq_def] at hloop
      cases hs : step state with
      | fail e => rw [hs] at hloop; cases hloop
      | div => rw [hs] at hloop; cases hloop
      | ok flow =>
          rw [hs] at hloop
          cases flow with
          | done value =>
              change Result.ok value = Result.ok out at hloop
              have hout : value = out := by injection hloop
              subst out
              exact hdone state value hinv hs
          | cont stateNext =>
              change Aeneas.Std.loop step stateNext = Result.ok out at hloop
              have hlt := hdecrease state stateNext hs
              have hltm : measure stateNext < n := by omega
              have hinvNext := hcontinue state stateNext hinv hs
              exact ih (measure stateNext) hltm stateNext out rfl hinvNext hloop

#print axioms loop_invariant_property

end AspisR1S9LoopInvariantPropertyV1
