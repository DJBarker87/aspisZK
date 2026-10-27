import RPt_FIo_FieldCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_LoopInvariant
open Aeneas Aeneas.Std Result ControlFlow

/-- Partial correctness for the actual Result loop. Failures/divergence are
not replaced by successful reference executions. -/
theorem preserve {S V : Type} (body : S → Result (ControlFlow S V))
    (inv : S → Prop) (post : V → Prop) (measure : S → Nat)
    (step : ∀ s, inv s → ∀ r, body s=ok r →
      match r with
      | .done v => post v
      | .cont t => inv t ∧ measure t<measure s)
    (s : S) (v : V) (initial : inv s) (run : loop body s=ok v) : post v := by
  suffices ∀ n s, measure s=n → inv s → loop body s=ok v → post v from
    this (measure s) s rfl initial run
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hs initial run
    rw [loop] at run
    cases hb : body s with
    | fail e => simp only [hb] at run; cases run
    | div => simp only [hb] at run; cases run
    | ok r =>
      simp only [hb] at run
      have h := step s initial r hb
      cases r with
      | done out =>
        have same : out=v := Result.ok.inj run
        exact same ▸ h
      | cont t =>
        exact ih (measure t) (by omega) t rfl h.1 run

#print axioms preserve
end AspisR1.FIo_LoopInvariant
end
