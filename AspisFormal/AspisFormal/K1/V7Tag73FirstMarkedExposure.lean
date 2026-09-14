import AspisFormal.K1.V7Tag73FiniteTapeLaw

/-!
# A once-only predictable exposure under the actual finite iid tape law

`mark state` is evaluated BEFORE the next answer. Once it returns a target,
this observer stops. This makes the unit budget structural, not a premise
about a retrospectively chosen child. The observed state may retain ALL past
answers and arbitrary dependent continuations. It cannot read the unconsumed
tape, because that tape is not an input to `mark` or `next`.

Selecting the last successful child after seeing all answers does not satisfy
this interface merely by declaring a `mark` function.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73FirstMarkedExposure
open MeasureTheory
open scoped BigOperators
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73FiniteTapeLaw
noncomputable section
variable {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
variable {State : Type*}

def firstMarkedHit (next : State → A → State)
    (mark : State → Option (Finset A)) :
    (n : Nat) → State → FreshAnswerTape A n → Prop
  | 0, _, _ => False
  | n + 1, s, t => match mark s with
    | some target => t.1 ∈ target
    | none => firstMarkedHit next mark n (next s t.1) t.2

def markedEvent (next : State → A → State)
    (mark : State → Option (Finset A)) (n : Nat) (s : State) :
    Set (FreshAnswerTape A n) := {t | firstMarkedHit next mark n s t}

/-- A disabled observer cannot report a hit. -/
theorem disabled_never_hits (next : State → A → State) (n : Nat)
    (s : State) (t : FreshAnswerTape A n) :
    ¬ firstMarkedHit next (fun _ => none) n s t := by
  induction n generalizing s with
  | zero => exact id
  | succ n ih => exact ih (next s t.1) t.2

/-- This is the missing zero-extra-union calculation. Targets can differ at
all earlier histories, but only the FIRST selected target is tested. -/
theorem firstMarked_probability_le (law : PMF A)
    (next : State → A → State) (mark : State → Option (Finset A))
    (error : ENNReal)
    (localBound : ∀ s target, mark s = some target →
      law.toOuterMeasure (target : Set A) ≤ error)
    (n : Nat) (s : State) :
    (iidTape law n).toOuterMeasure (markedEvent next mark n s) ≤ error := by
  classical
  induction n generalizing s with
  | zero => simp [markedEvent, firstMarkedHit]
  | succ n ih =>
      cases hm : mark s with
      | some target =>
          have eventEq : markedEvent next mark (n + 1) s =
              {t : FreshAnswerTape A (n + 1) | t.1 ∈ target} := by
            ext t
            simp [markedEvent, firstMarkedHit, hm]
          rw [eventEq, iidTape_head_event]
          exact localBound s target hm
      | none =>
          rw [iidTape_event_succ]
          calc
            (∑ a, law a * (iidTape law n).toOuterMeasure
                {tail | (a, tail) ∈ markedEvent next mark (n + 1) s}) ≤
                ∑ a, law a * error := by
              apply Finset.sum_le_sum
              intro a _
              apply mul_le_mul_left'
              simpa only [markedEvent, firstMarkedHit, hm] using ih (next s a)
            _ = error := by
              rw [← Finset.sum_mul]
              have total : (∑ a, law a) = 1 := by
                simpa only [tsum_fintype] using law.tsum_coe
              rw [total, one_mul]

/-- Cardinality form for an explicitly uniform alphabet. -/
theorem firstMarked_uniform_probability_le
    (next : State → A → State) (mark : State → Option (Finset A))
    (cap : Nat) (targetCap : ∀ s target, mark s = some target → target.card ≤ cap)
    (n : Nat) (s : State) :
    (PMF.uniformOfFintype (FreshAnswerTape A n)).toOuterMeasure
        (markedEvent next mark n s) ≤
      (cap : ENNReal) / (Fintype.card A : ENNReal) := by
  rw [← iidTape_uniform]
  apply firstMarked_probability_le
  intro state target marked
  rw [uniform_finset_mass]
  apply ENNReal.div_le_div_right
  exact_mod_cast targetCap state target marked

/-- An acceptance restriction is applied WITHOUT conditioning/renormalizing. -/
theorem restricted_firstMarked_probability_le (law : PMF A)
    (next : State → A → State) (mark : State → Option (Finset A))
    (error : ENNReal)
    (localBound : ∀ s target, mark s = some target →
      law.toOuterMeasure (target : Set A) ≤ error)
    (n : Nat) (s : State) (accept : Set (FreshAnswerTape A n)) :
    (iidTape law n).toOuterMeasure
        (accept ∩ markedEvent next mark n s) ≤ error :=
  ((iidTape law n).toOuterMeasure.mono Set.inter_subset_right).trans
    (firstMarked_probability_le law next mark error localBound n s)

#print axioms firstMarked_probability_le
#print axioms firstMarked_uniform_probability_le
#print axioms restricted_firstMarked_probability_le
end
end AspisK1.V7Tag73FirstMarkedExposure
