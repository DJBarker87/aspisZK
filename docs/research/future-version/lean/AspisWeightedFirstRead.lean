import DecodedFirstReadTraceBridge
import DecodedFirstReadReplay

/-! Per-step accounting, piece (a): the decoded first-read union bound with a
charge per start instead of one common charge.

Kind of result: a generic probability theorem about the memoized lazy-oracle
law of an arbitrary oracle program and an arbitrary causal decoder (the same
level as R1's `DecodedFirstReadUnionBound.decoded_first_read_bound`, which it
generalises). It says nothing about the Aspis transcript by itself; pieces (b)
and (c) instantiate it.

The charge `wt i t` of a fresh decoded start at address `i` is a function of
the address and of the table BEFORE the oracle answer at `i` is drawn, so the
remaining budget after the start does not depend on that answer.

* `WeightedReadsBound`: pathwise weighted budget (R1: `DecoderReadsBound`).
* `weighted_decoded_first_read_bound`: hit mass ≤ budget (R1:
  `decoded_first_read_bound`, mass ≤ N * ε).
* `uniform_weighted_of_count`, `decoded_first_read_bound_via_weighted`: the R1
  theorem recovered as the one-charge special case (a check of the
  generalisation against the proved R1 statement).
* `decoderFirstWeight`, `weightedReadsBound_of_traces`: trace form (R1:
  `decoderFirstReads`, `decoderReadsBound_of_traces`).
* `decoderFirstWeight_append`, `decoderFirstWeight_le_count_mul`,
  `decoderFirstWeight_const`: trace arithmetic used by piece (c). -/
set_option autoImplicit false
noncomputable section
namespace AspisPerStep.WeightedFirstRead
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open AspisR1.DecodedFirstReadUnionBound
attribute [local instance] Classical.propDecidable

/-- Pathwise weighted budget. At a fresh address where the decoder starts a
chain, the budget drops by that start's charge `wt i t`; memoized repeats and
decoder-rejected addresses cost nothing. At the end the budget must be
nonnegative. -/
def WeightedReadsBound {X M C I A Y O : Type} [DecidableEq I]
    (dec : Dec X M C I A Y) (wt : I → Table I A → ℚ) :
    Program I A O → Table I A → ℚ → Prop
  | .done _, _, W => 0 ≤ W
  | .ask i next, t, W =>
    match t i with
    | some a => WeightedReadsBound dec wt (next a) t W
    | none => if dec i t = none then
        ∀ a, WeightedReadsBound dec wt (next a) (put t i a) W
      else ∀ a, WeightedReadsBound dec wt (next a) (put t i a) (W - wt i t)

/-- Piece (a). If every decoded start's bad mass is at most its own charge,
the probability that some decoded chain hits its bad set is at most the
pathwise weighted budget. -/
theorem weighted_decoded_first_read_bound {X M C Pf I A Y : Type} [DecidableEq I]
    [Inhabited A] [Fintype A] [Nonempty A]
    (dec : Dec X M C I A Y) (bad : Prefix X M C → M → Table I A → C → Prop)
    (wt : I → Table I A → ℚ) (q : Program I A (Pf × Bool)) (t : Table I A) (W : ℚ)
    (hbad : ∀ (a : I) (T : Table I A) own pend g, dec a T = some (own, pend, g) →
      blaw g (fun out => indicator (bad out.1 out.2.1 T out.2.2)) own pend ≤ wt a T)
    (hW : WeightedReadsBound dec wt q t W) :
    lazyMean q t (fun v => indicator (hitsChain3 dec bad t v.1)) ≤ W := by
  induction q generalizing t W with
  | done o =>
      change indicator (hitsChain3 dec bad t []) ≤ _
      simp only [hitsChain3, indicator_false]
      simpa only [WeightedReadsBound] using hW
  | ask i next ih =>
      cases ht : t i with
      | some a =>
          simp only [lazyMean, ht]
          simp only [WeightedReadsBound, ht] at hW
          calc lazyMean (next a) t (fun r => indicator (hitsChain3 dec bad t ((i, a) :: r.1)))
              = lazyMean (next a) t (fun r => indicator (hitsChain3 dec bad t r.1)) := by
                apply lazyMean_congr
                intro v
                apply indicator_iff
                simp only [hitsChain3, put_self t i a ht, ht]
                simp
            _ ≤ W := ih a t W hW
      | none =>
          simp only [lazyMean, ht]
          by_cases hdnone : dec i t = none
          · simp only [WeightedReadsBound, ht, hdnone, if_true] at hW
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
              _ ≤ mean (fun _ : A => W) := by
                apply mean_mono
                intro a
                exact ih a (put t i a) W (hW a)
              _ = _ := mean_const _
          · simp only [WeightedReadsBound, ht, if_neg hdnone] at hW
            obtain ⟨⟨own, pend, g⟩, hS⟩ : ∃ r, dec i t = some r :=
              Option.ne_none_iff_exists'.mp hdnone
            let start : A → View I A (Pf × Bool) → Prop := fun a v =>
              ∃ own pend g P m c, dec i t = some (own, pend, g) ∧
                bfollow g ((i, a) :: v.1) own pend t = some (P, m, c) ∧ bad P m t c
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
            have hchain : mean (fun a => lazyMean (next a) (put t i a)
                (fun v => indicator (start a v))) ≤ wt i t :=
              calc mean (fun a => lazyMean (next a) (put t i a) (fun v => indicator (start a v)))
                  = mean (fun a => lazyMean (next a) (put t i a)
                      (fun v => indicator (∃ out, bfollow g ((i, a) :: v.1) own pend t = some out ∧
                        bad out.1 out.2.1 t out.2.2))) :=
                    mean_congr fun a => lazyMean_congr _ _ fun v => indicator_iff (hs a v)
                _ ≤ _ := key
                _ ≤ wt i t := hbad i t own pend g hS
            have step : ∀ a : A,
                lazyMean (next a) (put t i a) (fun r => indicator (hitsChain3 dec bad t ((i, a) :: r.1))) ≤
                  lazyMean (next a) (put t i a) (fun v => indicator (start a v)) + (W - wt i t) := by
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
                _ ≤ lazyMean (next a) (put t i a) (fun v => indicator (start a v)) + (W - wt i t) := by
                    have := ih a (put t i a) (W - wt i t) (hW a)
                    linarith
            calc mean (fun a => lazyMean (next a) (put t i a)
                    (fun r => indicator (hitsChain3 dec bad t ((i, a) :: r.1))))
                ≤ mean (fun a => lazyMean (next a) (put t i a) (fun v => indicator (start a v)) +
                    (W - wt i t)) := mean_mono step
              _ = mean (fun a => lazyMean (next a) (put t i a) (fun v => indicator (start a v))) +
                    (W - wt i t) := by rw [mean_add, mean_const]
              _ ≤ wt i t + (W - wt i t) := by linarith [hchain]
              _ = W := by ring

/-- One common charge: R1's count budget gives the weighted budget `N * ε`. -/
theorem uniform_weighted_of_count {X M C I A Y O : Type} [DecidableEq I]
    (dec : Dec X M C I A Y) (ε : ℚ) (hε : 0 ≤ ε) :
    ∀ (q : Program I A O) (t : Table I A) (N : Nat),
      DecoderReadsBound dec q t N → WeightedReadsBound dec (fun _ _ => ε) q t ((N : ℚ) * ε) := by
  intro q
  induction q with
  | done o => intro t N _; change 0 ≤ (N : ℚ) * ε; positivity
  | ask i next ih =>
    intro t N hN
    cases ht : t i with
    | some a =>
      simp only [DecoderReadsBound, ht] at hN
      simp only [WeightedReadsBound, ht]
      exact ih a t N hN
    | none =>
      by_cases hd : dec i t = none
      · simp only [DecoderReadsBound, ht, hd, if_true] at hN
        simp only [WeightedReadsBound, ht, hd, if_true]
        intro a
        exact ih a (put t i a) N (hN a)
      · simp only [DecoderReadsBound, ht, if_neg hd] at hN
        simp only [WeightedReadsBound, ht, if_neg hd]
        intro a
        have h := ih a (put t i a) (N - 1) (hN.2 a)
        have hcast : ((N - 1 : Nat) : ℚ) = (N : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [hcast] at h
        have heq : (N : ℚ) * ε - ε = ((N : ℚ) - 1) * ε := by ring
        rw [heq]
        exact h

/-- The R1 theorem as the one-charge special case of piece (a). Same
hypotheses and conclusion as `DecodedFirstReadUnionBound.decoded_first_read_bound`. -/
theorem decoded_first_read_bound_via_weighted {X M C Pf I A Y : Type} [DecidableEq I]
    [Inhabited A] [Fintype A] [Nonempty A]
    (dec : Dec X M C I A Y) (bad : Prefix X M C → M → Table I A → C → Prop)
    (ε : ℚ) (q : Program I A (Pf × Bool)) (t : Table I A) (N : Nat) (hε : 0 ≤ ε)
    (hbad : ∀ (a : I) (T : Table I A) own pend g, dec a T = some (own, pend, g) →
      blaw g (fun out => indicator (bad out.1 out.2.1 T out.2.2)) own pend ≤ ε)
    (hN : DecoderReadsBound dec q t N) :
    lazyMean q t (fun v => indicator (hitsChain3 dec bad t v.1)) ≤ (N : ℚ) * ε :=
  weighted_decoded_first_read_bound dec bad (fun _ _ => ε) q t ((N : ℚ) * ε) hbad
    (uniform_weighted_of_count dec ε hε q t N hN)

/-- Weighted count of fresh decoded starts on a chronological trace. -/
def decoderFirstWeight {X M C I A Y : Type} [DecidableEq I]
    (dec : Dec X M C I A Y) (wt : I → Table I A → ℚ) : Table I A → List (I × A) → ℚ
  | _, [] => 0
  | t, (i, a) :: rest =>
    (if t i = none ∧ dec i t ≠ none then wt i t else 0) +
      decoderFirstWeight dec wt (put t i a) rest

/-- Trace form: a weighted trace bound valid for every oracle supplies the
pathwise weighted budget. -/
theorem weightedReadsBound_of_traces {X M C I A Y O : Type} [DecidableEq I] [Nonempty A]
    (dec : Dec X M C I A Y) (wt : I → Table I A → ℚ) (p : Program I A O) :
    ∀ (t : Table I A) (W : ℚ),
      (∀ H : I → A, decoderFirstWeight dec wt t (eval (complete t H) p).1 ≤ W) →
      WeightedReadsBound dec wt p t W := by
  induction p with
  | done o =>
    intro t W hW
    obtain ⟨a⟩ := (inferInstance : Nonempty A)
    have hb := hW (fun _ => a)
    simpa only [WeightedReadsBound, eval, decoderFirstWeight] using hb
  | ask i next ih =>
    intro t W hW
    cases ht : t i with
    | some a =>
      simp only [WeightedReadsBound, ht]
      apply ih a t W
      intro H
      have hb := hW H
      simpa only [eval, complete_cached t H i a ht, decoderFirstWeight, ht,
        reduceCtorEq, false_and, if_false, zero_add, put_self t i a ht] using hb
    | none =>
      by_cases hd : dec i t = none
      · simp only [WeightedReadsBound, ht, hd, if_true]
        intro a
        apply ih a (put t i a) W
        intro H
        have hb := hW (Function.update H i a)
        simp only [eval, complete_missing t (Function.update H i a) i ht,
          Function.update_self, decoderFirstWeight, ht, hd, ne_eq,
          not_true_eq_false, and_false, if_false, zero_add] at hb
        rw [complete_resample t H i a ht] at hb
        exact hb
      · simp only [WeightedReadsBound, ht, if_neg hd]
        have hone : ∀ H : I → A, wt i t + decoderFirstWeight dec wt (put t i (H i))
            (eval (complete t H) (next (H i))).1 ≤ W := by
          intro H
          have hb := hW H
          simpa only [eval, complete_missing t H i ht, decoderFirstWeight, ht,
            hd, ne_eq, not_false_eq_true, and_self, if_true] using hb
        intro a
        apply ih a (put t i a) (W - wt i t)
        intro H
        have hb := hone (Function.update H i a)
        simp only [Function.update_self] at hb
        rw [complete_resample t H i a ht] at hb
        linarith

theorem decoderFirstWeight_append {X M C I A Y : Type} [DecidableEq I]
    (dec : Dec X M C I A Y) (wt : I → Table I A → ℚ)
    (t : Table I A) (pre tail : List (I × A)) :
    decoderFirstWeight dec wt t (pre ++ tail) =
      decoderFirstWeight dec wt t pre + decoderFirstWeight dec wt (applyTrace t pre) tail := by
  induction pre generalizing t with
  | nil => simp [decoderFirstWeight, applyTrace]
  | cons cell rest ih =>
    rcases cell with ⟨i, a⟩
    simp only [List.cons_append, decoderFirstWeight, applyTrace]
    rw [ih]
    ring

/-- With every charge at most `w`, the weighted count is at most the R1 count
times `w` (used for the adversary's queries in piece (c)). -/
theorem decoderFirstWeight_le_count_mul {X M C I A Y : Type} [DecidableEq I]
    (dec : Dec X M C I A Y) (wt : I → Table I A → ℚ) (w : ℚ)
    (hwt : ∀ i t, wt i t ≤ w) :
    ∀ (t : Table I A) (tr : List (I × A)),
      decoderFirstWeight dec wt t tr ≤ (decoderFirstReads dec t tr : ℚ) * w := by
  intro t tr
  induction tr generalizing t with
  | nil => simp [decoderFirstWeight, decoderFirstReads]
  | cons cell rest ih =>
    rcases cell with ⟨i, a⟩
    have h := ih (put t i a)
    simp only [decoderFirstWeight, decoderFirstReads]
    by_cases hc : t i = none ∧ dec i t ≠ none
    · rw [if_pos hc, if_pos hc]
      push_cast
      have := hwt i t
      linarith
    · rw [if_neg hc, if_neg hc]
      push_cast
      linarith

/-- With one common charge the weighted count is the R1 count times it. -/
theorem decoderFirstWeight_const {X M C I A Y : Type} [DecidableEq I]
    (dec : Dec X M C I A Y) (ε : ℚ) :
    ∀ (t : Table I A) (tr : List (I × A)),
      decoderFirstWeight dec (fun _ _ => ε) t tr = (decoderFirstReads dec t tr : ℚ) * ε := by
  intro t tr
  induction tr generalizing t with
  | nil => simp [decoderFirstWeight, decoderFirstReads]
  | cons cell rest ih =>
    rcases cell with ⟨i, a⟩
    simp only [decoderFirstWeight, decoderFirstReads, ih]
    split_ifs <;> push_cast <;> ring

#print axioms weighted_decoded_first_read_bound
#print axioms uniform_weighted_of_count
#print axioms decoded_first_read_bound_via_weighted
#print axioms weightedReadsBound_of_traces
#print axioms decoderFirstWeight_append
#print axioms decoderFirstWeight_le_count_mul
#print axioms decoderFirstWeight_const
end AspisPerStep.WeightedFirstRead
end
