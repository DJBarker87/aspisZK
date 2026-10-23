import Aeneas

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S9LoopOutputPropertyV1

/-- A successful Aeneas loop has a terminal body result.  If every successful
terminal step satisfies `P`, and every successful continuation strictly
decreases `measure`, then the loop's successful output satisfies `P`. -/
theorem loop_output_property {α β : Type}
    (step : α → Result (ControlFlow α β))
    (measure : α → Nat) (P : β → Prop)
    (hdone : ∀ s out, step s = .ok (.done out) → P out)
    (hdecrease : ∀ s s', step s = .ok (.cont s') → measure s' < measure s)
    : ∀ state out, Aeneas.Std.loop step state = .ok out → P out := by
  intro state out
  induction hm : measure state using Nat.strong_induction_on generalizing state out with
  | h n ih =>
      intro hloop
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
              exact hdone state value hs
          | cont stateNext =>
              change Aeneas.Std.loop step stateNext = Result.ok out at hloop
              have hlt := hdecrease state stateNext hs
              have hltm : measure stateNext < n := by omega
              exact ih (measure stateNext) hltm stateNext out rfl hloop

#print axioms loop_output_property

end AspisR1S9LoopOutputPropertyV1
