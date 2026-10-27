import R1Z.PV_RE_NoCatchCore
namespace R1Z.PV_RE_PoisonOutcomes
open Aeneas.Std
/-- The exact poisoning exclusion, including terminating error runs whose
error differs from the chosen poison. The invocation witness stays explicit. -/
theorem exclusion {I O : Type} (admitted : I → Prop)
    (run poisoned : I → Result O) (invoked : I → Prop) (poison : Error)
    (congruent : ∀ i, admitted i → poisoned i = run i)
    (absorption : ∀ i, admitted i → invoked i → poisoned i = .fail poison) :
    ∀ i, admitted i → run i ≠ .fail poison → ¬ invoked i := by
  intro i hi hn hr
  apply hn
  rw [← congruent i hi]
  exact absorption i hi hr

/-- An extracted outer .ok carrying a native Err remains eligible for
exclusion: rejection/retry exhaustion differs from outer Aeneas failure. -/
theorem outer_ok_not_poison {O : Type} (v : O) (e : Error) :
    (Result.ok v : Result O) ≠ .fail e := by
  intro h; cases h

/-- Exact absorption plus unchanged divergence also excludes a finite
invocation witnessing this error propagation. This is not a proof that a
callback is absent from a diverging native execution. -/
theorem divergence_not_poison {O : Type} (e : Error) :
    (Result.div : Result O) ≠ .fail e := by
  intro h; cases h

/-- Different outer error values also distinguish a reached poisoned call. -/
theorem different_error {O : Type} (original poison : Error)
    (h : original ≠ poison) :
    (Result.fail original : Result O) ≠ .fail poison := by
  intro he
  exact h (Result.fail.inj he)

#print axioms exclusion
#print axioms outer_ok_not_poison
#print axioms divergence_not_poison
#print axioms different_error
end R1Z.PV_RE_PoisonOutcomes
