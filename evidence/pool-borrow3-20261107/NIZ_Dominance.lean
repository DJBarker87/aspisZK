import NIZ_LAYOUT
set_option autoImplicit false
namespace NIZ_Dominance

/-- Finite prefixes that have not passed through the named source barrier. -/
inductive Avoids {V : Type} (edge : V → V → Prop) (barrier : V → Prop)
    (entry : V) : V → Prop where
  | initial : Avoids edge barrier entry entry
  | next {a b : V} (prior : Avoids edge barrier entry a)
      (step : edge a b) (notBarrier : ¬ barrier a) : Avoids edge barrier entry b

/-- Transcription of the native per-edge graph certificate assertion. -/
def EdgeCut {V : Type} (edge : V → V → Prop) (safe barrier : V → Prop) : Prop :=
  ∀ a b, edge a b → safe a → barrier a ∨ safe b

theorem avoiding_safe {V : Type} (edge : V → V → Prop) (safe barrier : V → Prop)
    (entry target : V) (initial : safe entry) (cut : EdgeCut edge safe barrier)
    (path : Avoids edge barrier entry target) : safe target := by
  induction path with
  | initial => exact initial
  | next prior step notBarrier ih =>
    rcases cut _ _ step ih with hit | next
    · exact False.elim (notBarrier hit)
    · exact next
#print axioms avoiding_safe

/-- CFG dominance, not a returned-Ok, cell-identity or whole-owner theorem. -/
theorem barrier_required {V : Type} (edge : V → V → Prop) (safe barrier : V → Prop)
    (entry target : V) (initial : safe entry) (cut : EdgeCut edge safe barrier)
    (guardOutside : ¬ safe target) : ¬ Avoids edge barrier entry target := by
  intro path
  exact guardOutside (avoiding_safe edge safe barrier entry target initial cut path)
#print axioms barrier_required
end NIZ_Dominance
