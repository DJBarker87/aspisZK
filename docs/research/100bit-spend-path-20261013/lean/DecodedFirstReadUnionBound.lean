import RawAdaptiveClassifierHitDensity

/-! Causal union bound charged only at fresh addresses where the input-table
transcript decoder can start a challenge chain. Internal hashes for which the
decoder returns none carry zero classifier-event charge. This counts event
opportunities directly; it does not assign security bits to computational work.
A concrete experiment's decoder-start budget remains a separate theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DecodedFirstReadUnionBound
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
attribute [local instance] Classical.propDecidable

/-- Pathwise count bound on fresh addresses at which this causal decoder
starts. Memoized repeats and decoder-rejected inputs do not spend the bound. -/
def DecoderReadsBound {X M C I A Y O : Type} [DecidableEq I]
    (dec : Dec X M C I A Y) : Program I A O → Table I A → Nat → Prop
  | .done _, _, _ => True
  | .ask i next, t, N =>
    match t i with
    | some a => DecoderReadsBound dec (next a) t N
    | none => if dec i t = none then
        ∀ a, DecoderReadsBound dec (next a) (put t i a) N
      else 0 < N ∧ ∀ a, DecoderReadsBound dec (next a) (put t i a) (N-1)

theorem decoded_first_read_bound {X M C Pf I A Y : Type} [DecidableEq I] [Inhabited A] [Fintype A] [Nonempty A]
    (dec : Dec X M C I A Y) (bad : Prefix X M C → M → Table I A → C → Prop)
    (ε : ℚ) (q : Program I A (Pf × Bool)) (t : Table I A) (N : Nat) (hε : 0 ≤ ε)
    (hbad : ∀ (a : I) (T : Table I A) own pend g, dec a T = some (own, pend, g) →
      blaw g (fun out => indicator (bad out.1 out.2.1 T out.2.2)) own pend ≤ ε)
    (hN : DecoderReadsBound dec q t N) :
    lazyMean q t (fun v => indicator (hitsChain3 dec bad t v.1)) ≤ (N : ℚ) * ε := by
  induction q generalizing t N with
  | done o =>
      change indicator (hitsChain3 dec bad t []) ≤ _
      simp only [hitsChain3, indicator_false]
      positivity
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          simp only [lazyMean, ht]
          simp only [DecoderReadsBound, ht] at hN
          calc lazyMean (next a) t (fun r => indicator (hitsChain3 dec bad t ((i, a) :: r.1)))
              = lazyMean (next a) t (fun r => indicator (hitsChain3 dec bad t r.1)) := by
                apply lazyMean_congr
                intro v
                apply indicator_iff
                simp only [hitsChain3, put_self t i a ht, ht]
                simp
            _ ≤ (N : ℚ) * ε := ih a t N hN
      | none =>
          simp only [lazyMean, ht]
          by_cases hdnone : dec i t = none
          · simp only [DecoderReadsBound, ht, hdnone, if_true] at hN
            calc
              _ = mean (fun a => lazyMean (next a) (put t i a)
                  (fun v => indicator (hitsChain3 dec bad (put t i a) v.1))) := by
                apply mean_congr
                intro a
                apply lazyMean_congr
                intro v
                apply indicator_iff
                simp only [hitsChain3, ht, true_and, hdnone,
                  reduceCtorEq, false_and]
                simp
              _ ≤ mean (fun _ : A => (N : ℚ) * ε) := by
                apply mean_mono
                intro a
                exact ih a (put t i a) N (hN a)
              _ = _ := mean_const _
          · simp only [DecoderReadsBound, ht, if_neg hdnone] at hN
            obtain ⟨hpos, hrest⟩ := hN
            let start : A → View I A (Pf × Bool) → Prop := fun a v =>
              ∃ own pend g P m c, dec i t = some (own, pend, g) ∧
                bfollow g ((i, a) :: v.1) own pend t = some (P, m, c) ∧ bad P m t c
            have hchain : mean (fun a => lazyMean (next a) (put t i a)
                (fun v => indicator (start a v))) ≤ ε := by
              by_cases hdec : ∃ own pend g, dec i t = some (own, pend, g)
              · obtain ⟨own, pend, g, hS⟩ := hdec
                have hs : ∀ a v, start a v ↔
                    ∃ out, bfollow g ((i, a) :: v.1) own pend t = some out ∧
                      bad out.1 out.2.1 t out.2.2 := by
                  intro a v
                  constructor
                  · rintro ⟨own', pend', g', P, m, c, hS', hf, hb⟩
                    rw [hS] at hS'
                    cases hS'
                    exact ⟨(P, m, c), hf, hb⟩
                  · rintro ⟨⟨P, m, c⟩, hf, hb⟩
                    exact ⟨own, pend, g, P, m, c, hS, hf, hb⟩
                have key : mean (fun a => lazyMean (next a) (put t i a)
                    (fun v => indicator (∃ out, bfollow g ((i, a) :: v.1) own pend t = some out ∧
                      bad out.1 out.2.1 t out.2.2))) ≤
                    blaw g (fun out => indicator (bad out.1 out.2.1 t out.2.2)) own pend := by
                  have hfull := chainB g (fun out => bad out.1 out.2.1 t out.2.2) (.ask i next) t own pend
                  simp only [lazyMean, ht] at hfull
                  exact hfull
                calc mean (fun a => lazyMean (next a) (put t i a) (fun v => indicator (start a v)))
                    = mean (fun a => lazyMean (next a) (put t i a)
                        (fun v => indicator (∃ out, bfollow g ((i, a) :: v.1) own pend t = some out ∧
                          bad out.1 out.2.1 t out.2.2))) :=
                      mean_congr fun a => lazyMean_congr _ _ fun v => indicator_iff (hs a v)
                  _ ≤ _ := key
                  _ ≤ ε := hbad i t own pend g hS
              · have hz : ∀ a v, ¬ start a v := by
                  rintro a v ⟨own, pend, g, _, _, _, hS, _, _⟩
                  exact hdec ⟨own, pend, g, hS⟩
                rw [mean_congr (fun a => lazyMean_congr _ _ (fun v =>
                  indicator_iff (iff_false_intro (hz a v))))]
                simp only [indicator_false]
                rw [mean_congr (fun a => lazyMean_const _ _ _), mean_const]
                exact hε
            have step : ∀ a : A,
                lazyMean (next a) (put t i a) (fun r => indicator (hitsChain3 dec bad t ((i, a) :: r.1))) ≤
                  lazyMean (next a) (put t i a) (fun v => indicator (start a v)) +
                    ((N - 1 : Nat) : ℚ) * ε := by
              intro a
              calc lazyMean (next a) (put t i a) (fun r => indicator (hitsChain3 dec bad t ((i, a) :: r.1)))
                  ≤ lazyMean (next a) (put t i a)
                      (fun v => indicator (start a v) + indicator (hitsChain3 dec bad (put t i a) v.1)) := by
                    apply lazyMean_mono
                    intro v
                    simp only [hitsChain3, ht, true_and]
                    exact indicator_or_le _ _
                _ = lazyMean (next a) (put t i a) (fun v => indicator (start a v)) +
                      lazyMean (next a) (put t i a) (fun v => indicator (hitsChain3 dec bad (put t i a) v.1)) :=
                    lazyMean_add _ _ _ _
                _ ≤ lazyMean (next a) (put t i a) (fun v => indicator (start a v)) +
                      ((N - 1 : Nat) : ℚ) * ε := by
                    have := ih a (put t i a) (N - 1) (hrest a)
                    linarith
            calc mean (fun a => lazyMean (next a) (put t i a)
                    (fun r => indicator (hitsChain3 dec bad t ((i, a) :: r.1))))
                ≤ mean (fun a => lazyMean (next a) (put t i a) (fun v => indicator (start a v)) +
                    ((N - 1 : Nat) : ℚ) * ε) := mean_mono step
              _ = mean (fun a => lazyMean (next a) (put t i a) (fun v => indicator (start a v))) +
                    ((N - 1 : Nat) : ℚ) * ε := by rw [mean_add, mean_const]
              _ ≤ ε + ((N - 1 : Nat) : ℚ) * ε := by linarith [hchain]
              _ = (N : ℚ) * ε := by
                  have : ((N - 1 : Nat) : ℚ) = (N : ℚ) - 1 := by
                    rw [Nat.cast_sub (by omega)]; simp
                  rw [this]; ring

#print axioms decoded_first_read_bound
end AspisR1.DecodedFirstReadUnionBound
end
