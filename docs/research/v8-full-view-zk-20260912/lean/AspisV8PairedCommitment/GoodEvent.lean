import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

/-!
Finite good-event utility. `Out` must include visible abort/retry/oracle events,
not only successes. Constructing agreement and bounding bad mass are separate.
-/
namespace AspisV8PairedCommitment

variable {Coin Out : Type*} [Fintype Coin]

def eventMass (weight : Coin → ℝ) (run : Coin → Out) (test : Out → Bool) : ℝ :=
  ∑ coin, if test (run coin) then weight coin else 0

def badMass (weight : Coin → ℝ) (bad : Coin → Bool) : ℝ :=
  ∑ coin, if bad coin then weight coin else 0

theorem indicator_difference_bound (weight : ℝ) (nonnegative : 0 ≤ weight)
    (a b : Bool) :
    |(if a then weight else 0) - (if b then weight else 0)| ≤ weight := by
  cases a <;> cases b <;> simp [abs_of_nonneg nonnegative, nonnegative]

theorem event_gap_le_bad_mass
    (weight : Coin → ℝ) (nonnegative : ∀ coin, 0 ≤ weight coin)
    (real ideal : Coin → Out) (bad : Coin → Bool)
    (agrees : ∀ coin, bad coin = false → real coin = ideal coin)
    (test : Out → Bool) :
    |eventMass weight real test - eventMass weight ideal test| ≤
      badMass weight bad := by
  unfold eventMass badMass
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ coin, ((if test (real coin) then weight coin else 0) -
        (if test (ideal coin) then weight coin else 0))| ≤
        ∑ coin, |(if test (real coin) then weight coin else 0) -
          (if test (ideal coin) then weight coin else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ coin, if bad coin then weight coin else 0 := by
      apply Finset.sum_le_sum
      intro coin _
      cases hb : bad coin with
      | false => simp [hb, agrees coin hb]
      | true =>
          simpa [hb] using indicator_difference_bound (weight coin)
            (nonnegative coin) (test (real coin)) (test (ideal coin))

#print axioms event_gap_le_bad_mass
end AspisV8PairedCommitment
