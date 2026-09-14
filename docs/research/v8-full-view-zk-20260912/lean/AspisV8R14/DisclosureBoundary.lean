import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Exact event identities before any sampling assumption. DRAFT: not compiled. -/
set_option autoImplicit false
namespace AspisV8R14
variable {World View : Type*}

/-- Extending a transcript cannot erase a public deterministic separator. -/
theorem separator_survives_extension
    {Full Small Scalar : Type*} (restrict : Full → Small)
    (stat : Small → Scalar) (left right : Full)
    (different : stat (restrict left) ≠ stat (restrict right)) : left ≠ right := by
  intro h; exact different (congrArg (fun v => stat (restrict v)) h)

/-- Source obligation: on a publicly recognised schedule event, both worlds
have different fixed public statistics. Nothing is conditioned away here. -/
def disclosureTest {S : Type*} [DecidableEq S]
    (event : View → Bool) (stat : View → S) (rightValue : S) (v : View) : Bool :=
  event v && decide (stat v = rightValue)

theorem right_disclosure_event {S : Type*} [DecidableEq S]
    (event : View → Bool) (stat : View → S) (v : View) (rightValue : S)
    (right : event v = true → stat v = rightValue) :
    disclosureTest event stat rightValue v = event v := by
  cases h : event v with
  | false => simp [disclosureTest, h]
  | true => simp [disclosureTest, h, right h]

theorem left_disclosure_impossible {S : Type*} [DecidableEq S]
    (event : View → Bool) (stat : View → S) (v : View) (leftValue rightValue : S)
    (different : leftValue ≠ rightValue)
    (left : event v = true → stat v = leftValue) :
    disclosureTest event stat rightValue v = false := by
  cases h : event v with
  | false => simp [disclosureTest, h]
  | true => simp [disclosureTest, h, left h, different]

/-- Any common simulator must pay for the distinguishing event somewhere.
This does not assert that the source's event has the ideal subset probability. -/
theorem two_simulator_errors_cover_gap (delta s e0 e1 : ℝ)
    (near0 : |s| ≤ e0) (near1 : |delta-s| ≤ e1) : delta ≤ e0+e1 := by
  have hs := (le_abs_self s).trans near0
  have hd := (le_abs_self (delta-s)).trans near1
  linarith

#print axioms separator_survives_extension
#print axioms right_disclosure_event
#print axioms left_disclosure_impossible
#print axioms two_simulator_errors_cover_gap
end AspisV8R14
