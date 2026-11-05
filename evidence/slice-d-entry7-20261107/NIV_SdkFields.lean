import NIV_FrameWindows
set_option autoImplicit false
namespace NIV_SdkFields

/-- Exact decoded Custom-code assertion from NIV_sdk::check. The range is
one of [0,32), [32,64), [64,76). It is a field observation, never a complete
SDK producer or output-success premise. See NIV_CERTIFICATES.md for hashes. -/
def fieldCut (low high : Nat) (expected : Nat → Nat) (code : Nat) : Prop :=
  low ≤ code / 256 ∧ code / 256 < high ∧ code % 256 = expected (code / 256)

theorem index (low high : Nat) (expected : Nat → Nat) (code : Nat)
    (cut : fieldCut low high expected code) :
    low ≤ code / 256 ∧ code / 256 < high := ⟨cut.1,cut.2.1⟩

theorem value (low high : Nat) (expected : Nat → Nat) (code : Nat)
    (cut : fieldCut low high expected code) :
    code % 256 = expected (code / 256) := cut.2.2

/-- Classes compose only for the SAME predicate/record at the SAME prefix.
This theorem cannot identify records or executions chosen independently. -/
theorem classes (P : Nat → Prop)
    (key : ∀ f, f < 32 → P f)
    (owner : ∀ f, 32 ≤ f → f < 64 → P f)
    (meta : ∀ f, 64 ≤ f → f < 76 → P f) : ∀ f, f < 76 → P f := by
  intro f bound
  by_cases first : f < 32
  · exact key f first
  · by_cases second : f < 64
    · exact owner f (by omega) second
    · exact meta f (by omega) bound

#print axioms index
#print axioms value
#print axioms classes
end NIV_SdkFields
