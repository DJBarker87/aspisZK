import PV_LIB_Observation
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SLICE_BoundedRun

/-- Canonical bounded natural-number search. The output is always obtained by
running the supplied deterministic machine; no output value is chosen from a
native-reply relation. The concrete adapters fix the acceptance test to the
provider's own completion/pending, frame and event-prefix predicates. -/
def fuel (bound : Nat) (accept : Nat → Prop) : Nat := by
  classical
  exact if h : ∃ n, n ≤ bound ∧ accept n then Nat.find h else 0

theorem selected (bound : Nat) (accept : Nat → Prop)
    (existsFuel : ∃ n, n ≤ bound ∧ accept n) :
    fuel bound accept ≤ bound ∧ accept (fuel bound accept) := by
  classical
  simpa only [fuel, dif_pos existsFuel] using Nat.find_spec existsFuel

theorem least (bound : Nat) (accept : Nat → Prop)
    (existsFuel : ∃ n, n ≤ bound ∧ accept n) (n : Nat)
    (eligible : n ≤ bound ∧ accept n) : fuel bound accept ≤ n := by
  classical
  simpa only [fuel, dif_pos existsFuel] using Nat.find_min' existsFuel eligible

#print axioms selected
#print axioms least
end PV_LIB_SLICE_BoundedRun
