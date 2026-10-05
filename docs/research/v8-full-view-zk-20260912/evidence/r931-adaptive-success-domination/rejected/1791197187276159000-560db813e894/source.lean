import AspisV8R19.R584IndependentBlockSampler

/-! Generic success-only domination for adaptive independent-answer programs.

This is deliberately a composition statement.  It assumes one supplied
per-step domination law and does not identify any source callback, oracle, or
state distribution.  `none` branches are retained by `run` and contribute
zero only to the designated success-only observer.
-/
set_option autoImplicit false
namespace AspisV8R19.R931AdaptiveSuccessDomination

open MemoizedProgramLaw OracleProgramOps OracleResampling AdaptiveFirstReadLaw
open R584IndependentBlockSampler
open scoped BigOperators

variable {I A S X : Type} [Fintype A] [Nonempty A] [Fintype X]
noncomputable section

/-- Run `n` adaptive stages.  A failed stage, or a later failed stage, remains
an explicit `none` result. -/
def run (step : Nat → S → Program I A (Option (X × S))) :
    Nat → Nat → S → Program I A (Option (List X × S))
  | i, 0, s => .done (some ([], s))
  | i, n + 1, s =>
      bind (step i s) (fun first =>
        match first with
        | none => .done none
        | some (x, t) =>
            bind (run step (i + 1) n t) (fun tail =>
              match tail with
              | none => .done none
              | some (xs, u) => .done (some (x :: xs, u))))

/-- The iterated upper-density functional over successful `X` outputs. -/
def weighted (mass : Nat → X → ℚ) :
    Nat → Nat → (List X → ℚ) → ℚ
  | _, 0, test => test []
  | i, n + 1, test =>
      ∑ x : X, mass i x * weighted mass (i + 1) n (fun xs => test (x :: xs))

private theorem outputMean_mono {O : Type} (p : Program I A O)
    {f g : O → ℚ} (h : ∀ o, f o ≤ g o) :
    outputMean p f ≤ outputMean p g := by
  induction p generalizing f g with
  | done o => exact h o
  | ask address next ih =>
      change mean (fun a => outputMean (next a) f) ≤
        mean (fun a => outputMean (next a) g)
      unfold mean
      apply div_le_div_of_nonneg_right
      · exact Finset.sum_le_sum (fun a _ => ih a h)
      · positivity

private theorem weighted_nonneg (mass : Nat → X → ℚ)
    (hmass : ∀ i x, 0 ≤ mass i x) :
    ∀ i n test, (∀ xs, 0 ≤ test xs) → 0 ≤ weighted mass i n test
  | i, 0, test, htest => htest []
  | i, n + 1, test, htest => by
      simp only [weighted]
      apply Finset.sum_nonneg
      intro x hx
      exact mul_nonneg (hmass i x)
        (weighted_nonneg mass hmass (i + 1) n (fun xs => test (x :: xs))
          (fun xs => htest (x :: xs)))

/-- A supplied one-step success density law composes through arbitrary returned
states and deterministic failure propagation. -/
theorem adaptive_success_domination
    (step : Nat → S → Program I A (Option (X × S)))
    (mass : Nat → X → ℚ)
    (hmass : ∀ i x, 0 ≤ mass i x)
    (hstep : ∀ i s f, (∀ x, 0 ≤ f x) →
      outputMean (step i s) (fun out => match out with | none => 0 | some v => f v.1) ≤
        ∑ x : X, mass i x * f x) :
    ∀ i n s test, (∀ xs, 0 ≤ test xs) →
      outputMean (run step i n s)
        (fun out => match out with | none => 0 | some v => test v.1) ≤ weighted mass i n test := by
  intro i n
  induction n generalizing i with
  | zero =>
      intro s test htest
      simp only [run, outputMean_done, weighted]
  | succ n ih =>
      intro s test htest
      rw [run, outputMean_bind]
      let f : X → ℚ := fun x => weighted mass (i + 1) n (fun xs => test (x :: xs))
      have hf : ∀ x, 0 ≤ f x := by
        intro x
        exact weighted_nonneg mass hmass (i + 1) n _ (fun xs => htest (x :: xs))
      have hcontinuation : ∀ first : Option (X × S),
          outputMean
            (match first with
            | none => .done none
            | some (x, t) =>
                bind (run step (i + 1) n t) (fun tail =>
                  match tail with
                  | none => .done none
                  | some (xs, u) => .done (some (x :: xs, u))))
            (fun out => match out with | none => 0 | some v => test v.1) ≤
          (match first with | none => 0 | some v => f v.1) := by
        intro first
        cases first with
        | none => exact le_rfl
        | some pair =>
            rcases pair with ⟨x, t⟩
            rw [outputMean_bind]
            have hpoint : ∀ tail : Option (List X × S),
                outputMean
                  (match tail with
                  | none => .done none
                  | some (xs, u) => .done (some (x :: xs, u)))
                  (fun out => match out with | none => 0 | some v => test v.1) =
                (match tail with | none => 0 | some v => test (x :: v.1)) := by
              intro tail
              cases tail <;> rfl
            rw [outputMean_congr _ hpoint]
            exact ih (i + 1) t (fun xs => test (x :: xs))
              (fun xs => htest (x :: xs))
      calc
        outputMean (step i s) (fun first =>
          outputMean
            (match first with
            | none => .done none
            | some (x, t) =>
                bind (run step (i + 1) n t) (fun tail =>
                  match tail with
                  | none => .done none
                  | some (xs, u) => .done (some (x :: xs, u))))
            (fun out => match out with | none => 0 | some v => test v.1)) ≤
          outputMean (step i s) (fun out => match out with | none => 0 | some v => f v.1) :=
            outputMean_mono (step i s) hcontinuation
        _ ≤ ∑ x : X, mass i x * f x := hstep i s f hf
        _ = weighted mass i (n + 1) test := by rfl

#print axioms outputMean_mono
#print axioms weighted_nonneg
#print axioms run
#print axioms weighted
#print axioms adaptive_success_domination

end
end AspisV8R19.R931AdaptiveSuccessDomination
