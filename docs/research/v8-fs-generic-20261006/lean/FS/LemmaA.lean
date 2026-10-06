import FS.Statement

/-! # Lemma A: first-read union bound

Induction on the memoised program.  At a cache hit the table is unchanged and
nothing is charged; at a first read the `none` branch of `lazyMean` is the
uniform fresh-answer law, and one `ε` is charged.  Addresses and stopping are
adaptive.  (`lazyMean_eq_independentMean` is not used: its `FreshFrom`
premise excludes cache hits, which the prover-then-verifier program has.) -/
set_option autoImplicit false
namespace FS

open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment

section Mean
variable {X : Type} [Fintype X]

theorem mean_mono {f g : X → ℚ} (h : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  unfold mean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

theorem mean_add (f g : X → ℚ) : mean (fun x => f x + g x) = mean f + mean g := by
  unfold mean
  rw [Finset.sum_add_distrib, add_div]

theorem mean_nonneg {f : X → ℚ} (h : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  unfold mean
  exact div_nonneg (Finset.sum_nonneg fun x _ => h x) (by positivity)

end Mean

theorem indicator_or_le (p q : Prop) : indicator (p ∨ q) ≤ indicator p + indicator q := by
  classical
  unfold indicator
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem indicator_mono {p q : Prop} (h : p → q) : indicator p ≤ indicator q := by
  classical
  unfold indicator
  by_cases hp : p
  · simp [hp, h hp]
  · simp only [hp, if_false]
    split <;> norm_num

theorem indicator_false : indicator False = 0 := by
  classical
  simp [indicator]

theorem indicator_iff {p q : Prop} (h : p ↔ q) : indicator p = indicator q := by
  classical
  simp only [indicator, h]

section Lazy
variable {I A O : Type} [DecidableEq I] [Fintype A]

theorem lazyMean_congr (p : Program I A O) (t : Table I A) {f g : View I A O → ℚ}
    (h : ∀ v, f v = g v) : lazyMean p t f = lazyMean p t g := by
  induction p generalizing t f g with
  | done o => exact h _
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          simp only [lazyMean, ht]
          exact ih a t (fun r => h _)
      | none =>
          simp only [lazyMean, ht]
          exact mean_congr fun a => ih a (put t i a) (fun r => h _)

theorem lazyMean_mono (p : Program I A O) (t : Table I A) {f g : View I A O → ℚ}
    (h : ∀ v, f v ≤ g v) : lazyMean p t f ≤ lazyMean p t g := by
  induction p generalizing t f g with
  | done o => exact h _
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          simp only [lazyMean, ht]
          exact ih a t (fun r => h _)
      | none =>
          simp only [lazyMean, ht]
          exact mean_mono fun a => ih a (put t i a) (fun r => h _)

theorem lazyMean_add (p : Program I A O) (t : Table I A) (f g : View I A O → ℚ) :
    lazyMean p t (fun v => f v + g v) = lazyMean p t f + lazyMean p t g := by
  induction p generalizing t f g with
  | done o => rfl
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          simp only [lazyMean, ht]
          exact ih a t _ _
      | none =>
          simp only [lazyMean, ht]
          rw [← mean_add]
          exact mean_congr fun a => ih a (put t i a) _ _

theorem lazyMean_const [Nonempty A] (p : Program I A O) (t : Table I A) (c : ℚ) :
    lazyMean p t (fun _ => c) = c := by
  induction p generalizing t with
  | done o => rfl
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          simp only [lazyMean, ht]
          exact ih a t
      | none =>
          simp only [lazyMean, ht]
          rw [mean_congr fun a => ih a (put t i a)]
          exact mean_const c

end Lazy

theorem put_self {I A : Type} [DecidableEq I] (t : Table I A) (i : I) (a : A)
    (h : t i = some a) : put t i a = t := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [put, h]
  · simp [put, hj]

/-- Lemma A. -/
theorem lemmaA : LemmaA := by
  intro I A O _ _ _ p t N bad ε hε hbad hN
  induction p generalizing t N with
  | done o =>
      change indicator (hitsBad bad t []) ≤ _
      simp only [hitsBad, indicator_false]
      positivity
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          simp only [lazyMean, ht]
          simp only [FirstReadsBound, ht] at hN
          calc lazyMean (next a) t (fun r => indicator (hitsBad bad t ((i, a) :: r.1)))
              = lazyMean (next a) t (fun r => indicator (hitsBad bad t r.1)) := by
                apply lazyMean_congr
                intro v
                apply indicator_iff
                simp only [hitsBad, put_self t i a ht, ht]
                simp
            _ ≤ (N : ℚ) * ε := ih a t N hN
      | none =>
          simp only [lazyMean, ht]
          simp only [FirstReadsBound, ht] at hN
          obtain ⟨hpos, hrest⟩ := hN
          have step : ∀ a : A,
              lazyMean (next a) (put t i a) (fun r => indicator (hitsBad bad t ((i, a) :: r.1))) ≤
                indicator (bad i t a) + ((N - 1 : Nat) : ℚ) * ε := by
            intro a
            calc lazyMean (next a) (put t i a) (fun r => indicator (hitsBad bad t ((i, a) :: r.1)))
                ≤ lazyMean (next a) (put t i a)
                    (fun r => indicator (bad i t a) + indicator (hitsBad bad (put t i a) r.1)) := by
                  apply lazyMean_mono
                  intro v
                  simp only [hitsBad, ht, true_and]
                  exact indicator_or_le _ _
              _ = indicator (bad i t a) +
                    lazyMean (next a) (put t i a) (fun r => indicator (hitsBad bad (put t i a) r.1)) := by
                  rw [lazyMean_add, lazyMean_const]
              _ ≤ indicator (bad i t a) + ((N - 1 : Nat) : ℚ) * ε := by
                  have := ih a (put t i a) (N - 1) (hrest a)
                  linarith
          calc mean (fun a => lazyMean (next a) (put t i a)
                  (fun r => indicator (hitsBad bad t ((i, a) :: r.1))))
              ≤ mean (fun a => indicator (bad i t a) + ((N - 1 : Nat) : ℚ) * ε) :=
                mean_mono step
            _ = mean (fun a => indicator (bad i t a)) + ((N - 1 : Nat) : ℚ) * ε := by
                rw [mean_add, mean_const]
            _ ≤ ε + ((N - 1 : Nat) : ℚ) * ε := by linarith [hbad i t]
            _ = (N : ℚ) * ε := by
                have : ((N - 1 : Nat) : ℚ) = (N : ℚ) - 1 := by
                  rw [Nat.cast_sub (by omega)]; simp
                rw [this]; ring

#print axioms lemmaA
end FS
