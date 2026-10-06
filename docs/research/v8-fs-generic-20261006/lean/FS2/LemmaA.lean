import FS2.Statement
import FS.LemmaA

/-! # The embedded-chain lemma and Lemma A′

`chainLemma`: along any continuation program, the mass of "the sampler's
cells are first-read in order and its output is bad" is at most the
sampler's law on fresh answers.  Induction on the continuation; at a first
read of the sampler's current cell the fresh `mean` of `lazyMean` matches the
fresh `mean` of `independentMean`; other first reads and all cache hits leave
the sampler where it is.

`lemmaA`: v1's induction, charging the chain lemma's bound at every first
read that starts a decodable chain. -/
set_option autoImplicit false
namespace FS2

open FS AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment

section Chain
variable {I A C O : Type} [DecidableEq I] [Fintype A] [Nonempty A]

theorem independentMean_nonneg (s : Program I A C) {f : View I A C → ℚ}
    (h : ∀ w, 0 ≤ f w) : 0 ≤ independentMean s f := by
  induction s generalizing f with
  | done c => exact h _
  | ask i k ih =>
      simp only [independentMean]
      exact mean_nonneg fun a => ih a fun w => h _

theorem independentMean_outcome (s : Program I A C) (g : C → ℚ) (f : View I A C → ℚ)
    (h : ∀ w, f w = g w.2) :
    independentMean s f = independentMean s (fun w => g w.2) := by
  induction s generalizing f with
  | done c => exact h _
  | ask i k ih =>
      simp only [independentMean]
      exact mean_congr fun a => ih a _ fun w => h _

/-- `follow` of a completed sampler ignores the trace. -/
theorem follow_done (c : C) (t : Table I A) (tr : List (I × A)) :
    follow (.done c : Program I A C) t tr = some c := by
  cases tr <;> rfl

theorem chainLemma : ChainLemma := by
  intro I A C O _ _ _ q t s bad
  induction q generalizing t s with
  | done o =>
      cases s with
      | done c =>
          simp only [lazyMean, follow, independentMean, Option.some.injEq, exists_eq_left']
          exact le_rfl
      | ask j k =>
          simp only [lazyMean, follow]
          rw [indicator_iff (q := False) (by simp), indicator_false]
          exact independentMean_nonneg _ fun _ => indicator_nonneg _
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          simp only [lazyMean, ht]
          cases s with
          | done c =>
              rw [lazyMean_congr _ _ (fun v => indicator_iff (q := bad c) (by
                simp [follow_done]))]
              rw [lazyMean_const]
              exact le_rfl
          | ask j k =>
              by_cases hij : i = j
              · subst hij
                rw [lazyMean_congr _ _ (fun v => indicator_iff (q := False) (by
                  simp [follow, ht]))]
                rw [lazyMean_const, indicator_false]
                exact independentMean_nonneg _ fun _ => indicator_nonneg _
              · have hstep : ∀ v : View I A O,
                    (∃ c, follow (.ask j k) t ((i, a) :: v.1) = some c ∧ bad c) ↔
                    (∃ c, follow (.ask j k) t v.1 = some c ∧ bad c) := by
                  intro v
                  simp only [follow, hij, if_false, put_self t i a ht]
                rw [lazyMean_congr _ _ (fun v => indicator_iff (hstep v))]
                exact ih a t (.ask j k)
      | none =>
          simp only [lazyMean, ht]
          cases s with
          | done c =>
              rw [mean_congr (fun a => lazyMean_congr _ _ (fun v =>
                indicator_iff (q := bad c) (by simp [follow_done])))]
              rw [mean_congr (fun a => lazyMean_const _ _ _), mean_const]
              exact le_rfl
          | ask j k =>
              by_cases hij : i = j
              · subst hij
                have hstep : ∀ (a : A) (v : View I A O),
                    (∃ c, follow (.ask i k) t ((i, a) :: v.1) = some c ∧ bad c) ↔
                    (∃ c, follow (k a) (put t i a) v.1 = some c ∧ bad c) := by
                  intro a v
                  simp only [follow, if_true, ht]
                simp only [independentMean]
                apply mean_mono
                intro a
                rw [lazyMean_congr _ _ (fun v => indicator_iff (hstep a v))]
                exact ih a (put t i a) (k a)
              · have hstep : ∀ (a : A) (v : View I A O),
                    (∃ c, follow (.ask j k) t ((i, a) :: v.1) = some c ∧ bad c) ↔
                    (∃ c, follow (.ask j k) (put t i a) v.1 = some c ∧ bad c) := by
                  intro a v
                  simp only [follow, hij, if_false]
                calc mean (fun a => lazyMean (next a) (put t i a)
                      (fun v => indicator (∃ c, follow (.ask j k) t ((i, a) :: v.1) = some c ∧ bad c)))
                    = mean (fun a => lazyMean (next a) (put t i a)
                      (fun v => indicator (∃ c, follow (.ask j k) (put t i a) v.1 = some c ∧ bad c))) :=
                      mean_congr fun a => lazyMean_congr _ _ fun v => indicator_iff (hstep a v)
                  _ ≤ mean (fun _ : A => independentMean (.ask j k) (fun w => indicator (bad w.2))) :=
                      mean_mono fun a => ih a (put t i a) (.ask j k)
                  _ = _ := mean_const _

end Chain

/-! ## Lemma A′ -/

theorem lemmaA : LemmaA := by
  intro X M C W Pf I A _ _ _ pr bad ε q t N hε hbad hN
  induction q generalizing t N with
  | done o =>
      change indicator (hitsChain bad pr t []) ≤ _
      simp only [hitsChain, indicator_false]
      positivity
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          simp only [lazyMean, ht]
          simp only [FirstReadsBound, ht] at hN
          calc lazyMean (next a) t (fun r => indicator (hitsChain bad pr t ((i, a) :: r.1)))
              = lazyMean (next a) t (fun r => indicator (hitsChain bad pr t r.1)) := by
                apply lazyMean_congr
                intro v
                apply indicator_iff
                simp only [hitsChain, put_self t i a ht, ht]
                simp
            _ ≤ (N : ℚ) * ε := ih a t N hN
      | none =>
          simp only [lazyMean, ht]
          simp only [FirstReadsBound, ht] at hN
          obtain ⟨hpos, hrest⟩ := hN
          -- the chain-start term, as a function of the fresh answer
          let start : A → View I A (Pf × Bool) → Prop := fun a v =>
            ∃ (P : Prefix X M C) (m : M) (c : C), pr.decode i t = some (P, m) ∧
              follow (pr.samp P.round P m) t ((i, a) :: v.1) = some c ∧ bad P m t c
          have hchain : mean (fun a => lazyMean (next a) (put t i a)
              (fun v => indicator (start a v))) ≤ ε := by
            by_cases hdec : ∃ (P : Prefix X M C) (m : M), pr.decode i t = some (P, m)
            · obtain ⟨P, m, hPm⟩ := hdec
              have hs : ∀ a v, start a v ↔
                  ∃ c, follow (pr.samp P.round P m) t ((i, a) :: v.1) = some c ∧ bad P m t c := by
                intro a v
                constructor
                · rintro ⟨P', m', c, hPm', hf, hb⟩
                  rw [hPm] at hPm'
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hPm')
                  exact ⟨c, hf, hb⟩
                · rintro ⟨c, hf, hb⟩
                  exact ⟨P, m, c, hPm, hf, hb⟩
              -- the chain lemma applied one step in: `mean` over the fresh answer
              have key : mean (fun a => lazyMean (next a) (put t i a)
                  (fun v => indicator (∃ c, follow (pr.samp P.round P m) t ((i, a) :: v.1) = some c ∧
                    bad P m t c))) ≤
                  independentMean (pr.samp P.round P m) (fun w => indicator (bad P m t w.2)) := by
                have hfull := chainLemma (.ask i next) t (pr.samp P.round P m) (bad P m t)
                simp only [lazyMean, ht] at hfull
                exact hfull
              calc mean (fun a => lazyMean (next a) (put t i a) (fun v => indicator (start a v)))
                  = mean (fun a => lazyMean (next a) (put t i a)
                      (fun v => indicator (∃ c, follow (pr.samp P.round P m) t ((i, a) :: v.1) = some c ∧
                        bad P m t c))) :=
                    mean_congr fun a => lazyMean_congr _ _ fun v => indicator_iff (hs a v)
                _ ≤ _ := key
                _ ≤ ε := hbad P m t
            · have hz : ∀ a v, ¬ start a v := by
                rintro a v ⟨P, m, c, hPm, _, _⟩
                exact hdec ⟨P, m, hPm⟩
              rw [mean_congr (fun a => lazyMean_congr _ _ (fun v =>
                indicator_iff (iff_false_intro (hz a v))))]
              simp only [indicator_false]
              rw [mean_congr (fun a => lazyMean_const _ _ _), mean_const]
              exact hε
          have step : ∀ a : A,
              lazyMean (next a) (put t i a) (fun r => indicator (hitsChain bad pr t ((i, a) :: r.1))) ≤
                lazyMean (next a) (put t i a) (fun v => indicator (start a v)) +
                  ((N - 1 : Nat) : ℚ) * ε := by
            intro a
            calc lazyMean (next a) (put t i a) (fun r => indicator (hitsChain bad pr t ((i, a) :: r.1)))
                ≤ lazyMean (next a) (put t i a)
                    (fun v => indicator (start a v) + indicator (hitsChain bad pr (put t i a) v.1)) := by
                  apply lazyMean_mono
                  intro v
                  simp only [hitsChain, ht, true_and]
                  exact indicator_or_le _ _
              _ = lazyMean (next a) (put t i a) (fun v => indicator (start a v)) +
                    lazyMean (next a) (put t i a) (fun v => indicator (hitsChain bad pr (put t i a) v.1)) :=
                  lazyMean_add _ _ _ _
              _ ≤ lazyMean (next a) (put t i a) (fun v => indicator (start a v)) +
                    ((N - 1 : Nat) : ℚ) * ε := by
                  have := ih a (put t i a) (N - 1) (hrest a)
                  linarith
          calc mean (fun a => lazyMean (next a) (put t i a)
                  (fun r => indicator (hitsChain bad pr t ((i, a) :: r.1))))
              ≤ mean (fun a => lazyMean (next a) (put t i a) (fun v => indicator (start a v)) +
                  ((N - 1 : Nat) : ℚ) * ε) := mean_mono step
            _ = mean (fun a => lazyMean (next a) (put t i a) (fun v => indicator (start a v))) +
                  ((N - 1 : Nat) : ℚ) * ε := by rw [mean_add, mean_const]
            _ ≤ ε + ((N - 1 : Nat) : ℚ) * ε := by linarith [hchain]
            _ = (N : ℚ) * ε := by
                have : ((N - 1 : Nat) : ℚ) = (N : ℚ) - 1 := by
                  rw [Nat.cast_sub (by omega)]; simp
                rw [this]; ring

#print axioms chainLemma
#print axioms lemmaA
end FS2
