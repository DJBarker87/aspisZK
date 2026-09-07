import AspisFormal.K1.V7Tag73K15ExactMeasureLedger

/-!
# Compiler-clean restriction of the Tag-73 K1.5 ledger

K1.6 charges the causal target event separately.  The upstream K1.5 theorem
therefore needs component bounds only after intersecting with the literal
compiler-clean event.  This leaf makes that restriction exact while retaining
the audited eight-category numerator and common denominator.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73K15RestrictedMeasureLedger

open MeasureTheory
open AspisK1.V7Tag73K15ExactMeasureLedger
open AspisV5ComponentCQM31TowerExact

/-- Restrict every one of the eight fixed K1.5 categories to the same clean
event. -/
def restrictFixedK15Events {Coins : Type} (clean : Set Coins)
    (events : FixedK15Events Coins) : FixedK15Events Coins where
  event category := clean ∩ events.event category

/-- Restriction commutes exactly with the finite category union. -/
theorem restrict_fixed_k15_failure_eq
    {Coins : Type} (clean : Set Coins) (events : FixedK15Events Coins) :
    (restrictFixedK15Events clean events).failure =
      clean ∩ events.failure := by
  ext sample
  simp only [restrictFixedK15Events, FixedK15Events.failure,
    Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨category, cleanMember, categoryMember⟩
    exact ⟨cleanMember, category, categoryMember⟩
  · rintro ⟨cleanMember, category, categoryMember⟩
    exact ⟨category, cleanMember, categoryMember⟩

/-- The existing exact eight-category ledger applies unchanged on a clean
slice.  No independence or additional union loss is introduced. -/
theorem restricted_fixed_k15_failure_probability_le
    {Coins : Type} (law : PMF Coins) (clean : Set Coins)
    (events : FixedK15Events Coins)
    (bounds : FixedK15EventBounds law
      (restrictFixedK15Events clean events)) :
    law.toOuterMeasure (clean ∩ events.failure) ≤
      (396430 : ENNReal) / ((P ^ 4 - 1 : Nat) : ENNReal) := by
  rw [← restrict_fixed_k15_failure_eq clean events]
  exact fixed_k15_failure_probability_le law
    (restrictFixedK15Events clean events) bounds

#print axioms restrict_fixed_k15_failure_eq
#print axioms restricted_fixed_k15_failure_probability_le

end AspisK1.V7Tag73K15RestrictedMeasureLedger
