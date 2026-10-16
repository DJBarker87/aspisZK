import FS2.Statement
import FS.LemmaA

/-! # The embedded-chain lemma and Lemma A′

`chainLemma`: along any continuation program, the mass of "the sampler's
cells are first-read (in any admissible order) and its output is bad" is at
most the sampler's law on fresh answers.  Induction on the continuation; at a
first read of a cell the sampler is waiting for, the fresh `mean` of
`lazyMean` matches the fresh `mean` of `independentMean` — for a `multi`,
consuming an arbitrary one of its cells first is the same law by commuting
the means (`multi_erase_mean`); other first reads and all cache hits leave
the sampler where it is.

`lemmaA`: v1's induction, charging the chain lemma's bound at every first
read that decodes to a completing sampler. -/
set_option autoImplicit false
namespace FS2

open FS AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment

section Chain
variable {I A C O : Type} [DecidableEq I] [Inhabited A] [Fintype A] [Nonempty A]

omit [DecidableEq I] [Inhabited A] [Nonempty A] in
theorem independentMean_nonneg (s : Program I A C) {f : View I A C → ℚ}
    (h : ∀ w, 0 ≤ f w) : 0 ≤ independentMean s f := by
  induction s generalizing f with
  | done c => exact h _
  | ask i k ih =>
      simp only [independentMean]
      exact mean_nonneg fun a => ih a fun w => h _

omit [DecidableEq I] [Inhabited A] [Nonempty A] in
theorem independentMean_outcome (s : Program I A C) (g : C → ℚ) (f : View I A C → ℚ)
    (h : ∀ w, f w = g w.2) :
    independentMean s f = independentMean s (fun w => g w.2) := by
  induction s generalizing f with
  | done c => exact h _
  | ask i k ih =>
      simp only [independentMean]
      exact mean_congr fun a => ih a _ fun w => h _

omit [Fintype A] [Nonempty A] in
/-- `follow` of a completed sampler ignores the trace. -/
theorem follow_done (c : C) (t : Table I A) (tr : List (I × A)) :
    follow (.done c : Sampler I A C) t tr = some c := by
  cases tr <;> rfl

omit [Nonempty A] in
theorem independentMean_ask (i : I) (k : A → Sampler I A C) (bad : C → Prop) :
    independentMean (Sampler.ask i k).toProgram (fun w => indicator (bad w.2)) =
      mean (fun a => independentMean (k a).toProgram (fun w => indicator (bad w.2))) := by
  simp only [Sampler.toProgram, independentMean]

/-- The law of a list of cells read in order. -/
noncomputable def listMean (bad : C → Prop) (cells : List I) (f : (I → A) → Program I A C) : ℚ :=
  independentMean (multiProg cells f) (fun w => indicator (bad w.2))

omit [Nonempty A] in
theorem listMean_nil (bad : C → Prop) (f : (I → A) → Program I A C) :
    listMean bad [] f = independentMean (f default) (fun w => indicator (bad w.2)) := rfl

omit [Nonempty A] in
theorem listMean_cons (bad : C → Prop) (c : I) (cs : List I) (f : (I → A) → Program I A C) :
    listMean bad (c :: cs) f =
      mean (fun a => listMean bad cs (fun acc => f (Function.update acc c a))) := by
  simp only [listMean, multiProg, independentMean]

omit [Nonempty A] in
theorem independentMean_multi (c : I) (cs : List I) (nd : (c :: cs).Nodup)
    (k : (I → A) → Sampler I A C) (bad : C → Prop) :
    independentMean (Sampler.multi c cs nd k).toProgram (fun w => indicator (bad w.2)) =
      listMean bad (c :: cs) (fun acc => (k acc).toProgram) := rfl

omit [Nonempty A] in
/-- Consuming any member cell first gives the same law. -/
theorem multi_erase_mean (bad : C → Prop) :
    ∀ (cells : List I) (f : (I → A) → Program I A C) (l : I), l ∈ cells →
      mean (fun a => listMean bad (cells.erase l) (fun acc => f (Function.update acc l a))) =
        listMean bad cells f := by
  intro cells
  induction cells with
  | nil => intro f l h; simp at h
  | cons c cs ih =>
      intro f l hl
      by_cases hlc : l = c
      · subst hlc
        rw [List.erase_cons_head, listMean_cons]
      · have hmem : l ∈ cs := by
          simp only [List.mem_cons] at hl
          exact hl.resolve_left hlc
        have herase : (c :: cs).erase l = c :: cs.erase l :=
          List.erase_cons_tail (by simpa using Ne.symm hlc)
        rw [herase]
        simp only [listMean_cons]
        rw [mean_comm]
        apply mean_congr
        intro b
        rw [← ih (fun acc => f (Function.update acc c b)) l hmem]
        apply mean_congr
        intro a
        congr 1
        funext acc
        rw [Function.update_comm (Ne.symm hlc)]

omit [Nonempty A] in
theorem stepMulti_mean (bad : C → Prop) (c : I) (cs : List I) (nd : (c :: cs).Nodup)
    (k : (I → A) → Sampler I A C) (l : I) (a : A) :
    independentMean (stepMulti c cs nd k l a).toProgram (fun w => indicator (bad w.2)) =
      listMean bad ((c :: cs).erase l) (fun acc => (k (Function.update acc l a)).toProgram) := by
  unfold stepMulti
  split
  · rename_i h
    rw [h, listMean_nil]
  · rename_i h
    conv_rhs => rw [h]
    rfl

theorem chainLemma : ChainLemma := by
  intro I A C O _ _ _ _ q t s bad
  induction q generalizing t s with
  | done o =>
      cases s with
      | done c =>
          simp only [lazyMean, follow, Sampler.toProgram, independentMean, Option.some.injEq,
            exists_eq_left']
          exact le_rfl
      | ask j k =>
          simp only [lazyMean, follow]
          rw [indicator_iff (q := False) (by simp), indicator_false]
          exact independentMean_nonneg _ fun _ => indicator_nonneg _
      | multi c cs nd k =>
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
          | multi c cs nd k =>
              by_cases hmem : i ∈ c :: cs
              · rw [lazyMean_congr _ _ (fun v => indicator_iff (q := False) (by
                  simp [follow, ht, hmem]))]
                rw [lazyMean_const, indicator_false]
                exact independentMean_nonneg _ fun _ => indicator_nonneg _
              · have hstep : ∀ v : View I A O,
                    (∃ c', follow (.multi c cs nd k) t ((i, a) :: v.1) = some c' ∧ bad c') ↔
                    (∃ c', follow (.multi c cs nd k) t v.1 = some c' ∧ bad c') := by
                  intro v
                  simp only [follow, hmem, if_false, put_self t i a ht]
                rw [lazyMean_congr _ _ (fun v => indicator_iff (hstep v))]
                exact ih a t (.multi c cs nd k)
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
                rw [independentMean_ask]
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
                  _ ≤ mean (fun _ : A => independentMean (Sampler.ask j k).toProgram
                        (fun w => indicator (bad w.2))) :=
                      mean_mono fun a => ih a (put t i a) (.ask j k)
                  _ = _ := mean_const _
          | multi c cs nd k =>
              by_cases hmem : i ∈ c :: cs
              · have hstep : ∀ (a : A) (v : View I A O),
                    (∃ c', follow (.multi c cs nd k) t ((i, a) :: v.1) = some c' ∧ bad c') ↔
                    (∃ c', follow (stepMulti c cs nd k i a) (put t i a) v.1 = some c' ∧ bad c') := by
                  intro a v
                  simp only [follow, hmem, if_true, ht]
                rw [independentMean_multi, ← multi_erase_mean bad (c :: cs) _ i hmem]
                apply mean_mono
                intro a
                rw [lazyMean_congr _ _ (fun v => indicator_iff (hstep a v))]
                have := ih a (put t i a) (stepMulti c cs nd k i a)
                rw [stepMulti_mean] at this
                exact this
              · have hstep : ∀ (a : A) (v : View I A O),
                    (∃ c', follow (.multi c cs nd k) t ((i, a) :: v.1) = some c' ∧ bad c') ↔
                    (∃ c', follow (.multi c cs nd k) (put t i a) v.1 = some c' ∧ bad c') := by
                  intro a v
                  simp only [follow, hmem, if_false]
                calc mean (fun a => lazyMean (next a) (put t i a)
                      (fun v => indicator (∃ c', follow (.multi c cs nd k) t ((i, a) :: v.1) = some c' ∧ bad c')))
                    = mean (fun a => lazyMean (next a) (put t i a)
                      (fun v => indicator (∃ c', follow (.multi c cs nd k) (put t i a) v.1 = some c' ∧ bad c'))) :=
                      mean_congr fun a => lazyMean_congr _ _ fun v => indicator_iff (hstep a v)
                  _ ≤ mean (fun _ : A => independentMean (Sampler.multi c cs nd k).toProgram
                        (fun w => indicator (bad w.2))) :=
                      mean_mono fun a => ih a (put t i a) (.multi c cs nd k)
                  _ = _ := mean_const _

end Chain

/-! ## Lemma A′ -/

theorem lemmaA : LemmaA := by
  intro X M C W Pf I A _ _ _ _ pr bad ε q t N hε hbad hN
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
          let start : A → View I A (Pf × Bool) → Prop := fun a v =>
            ∃ (S : Sampler I A (Prefix X M C × M × C)) (P : Prefix X M C) (m : M) (c : C),
              pr.decode i t = some S ∧ follow S t ((i, a) :: v.1) = some (P, m, c) ∧ bad P m t c
          have hchain : mean (fun a => lazyMean (next a) (put t i a)
              (fun v => indicator (start a v))) ≤ ε := by
            by_cases hdec : ∃ S, pr.decode i t = some S
            · obtain ⟨S, hS⟩ := hdec
              have hs : ∀ a v, start a v ↔
                  ∃ out, follow S t ((i, a) :: v.1) = some out ∧ bad out.1 out.2.1 t out.2.2 := by
                intro a v
                constructor
                · rintro ⟨S', P, m, c, hS', hf, hb⟩
                  rw [hS] at hS'
                  obtain rfl := Option.some.inj hS'
                  exact ⟨(P, m, c), hf, hb⟩
                · rintro ⟨⟨P, m, c⟩, hf, hb⟩
                  exact ⟨S, P, m, c, hS, hf, hb⟩
              have key : mean (fun a => lazyMean (next a) (put t i a)
                  (fun v => indicator (∃ out, follow S t ((i, a) :: v.1) = some out ∧
                    bad out.1 out.2.1 t out.2.2))) ≤
                  independentMean S.toProgram (fun w => indicator (bad w.2.1 w.2.2.1 t w.2.2.2)) := by
                have hfull := chainLemma (.ask i next) t S (fun out => bad out.1 out.2.1 t out.2.2)
                simp only [lazyMean, ht] at hfull
                exact hfull
              calc mean (fun a => lazyMean (next a) (put t i a) (fun v => indicator (start a v)))
                  = mean (fun a => lazyMean (next a) (put t i a)
                      (fun v => indicator (∃ out, follow S t ((i, a) :: v.1) = some out ∧
                        bad out.1 out.2.1 t out.2.2))) :=
                    mean_congr fun a => lazyMean_congr _ _ fun v => indicator_iff (hs a v)
                _ ≤ _ := key
                _ ≤ ε := hbad i t S hS
            · have hz : ∀ a v, ¬ start a v := by
                rintro a v ⟨S, _, _, _, hS, _, _⟩
                exact hdec ⟨S, hS⟩
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
