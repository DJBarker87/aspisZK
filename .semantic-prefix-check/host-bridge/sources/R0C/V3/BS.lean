import FS2.Theorem

/-! # Samplers with background reads

`BS` extends the FS2 sampler with `spawn c`: the cell `c` joins a background
set that may be first-read at any later time, in any order relative to the
sampler's own reads.  Its answer is recorded by position and handed to the
output function at the end.  The duplex q22 chain needs this: step `k+1`'s
addresses are determined by step `k`'s advance output, while the stop rule
depends on step `k`'s squeeze, which the prover may read late.

`chainB`: in any continuation program, the mass of "the sampler is followed
to completion with a bad output" is at most its law with every cell an
independent fresh answer (`blaw`). -/
set_option autoImplicit false
namespace R0C.V3

open FS AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment

inductive BS (I A X : Type)
  | done (x : X)
  | ask (i : I) (k : A → BS I A X)
  | spawn (c : I) (nxt : BS I A X)

section Defs
variable {I A X C : Type} [DecidableEq I] [Inhabited A]

def pushSpawns : BS I A X → List (I × Option A) → BS I A X × List (I × Option A)
  | .spawn c nxt, pend => pushSpawns nxt (pend ++ [(c, none)])
  | .done x, pend => (.done x, pend)
  | .ask i k, pend => (.ask i k, pend)

def allDone : List (I × Option A) → Bool
  | [] => true
  | (_, none) :: _ => false
  | (_, some _) :: rest => allDone rest

def answers (pend : List (I × Option A)) : List A := pend.map fun p => p.2.getD default

def finished (g : X → List A → C) : BS I A X → List (I × Option A) → Option C
  | .done x, pend => if allDone pend then some (g x (answers pend)) else none
  | .ask _ _, _ => none
  | .spawn _ _, _ => none

def waits (l : I) : List (I × Option A) → Bool
  | [] => false
  | (c, none) :: rest => decide (c = l) || waits l rest
  | (_, some _) :: rest => waits l rest

def record (l : I) (a : A) : List (I × Option A) → List (I × Option A)
  | [] => []
  | (c, none) :: rest => if c = l then (c, some a) :: rest else (c, none) :: record l a rest
  | (c, some b) :: rest => (c, some b) :: record l a rest

def ownCell : BS I A X → Option I
  | .done _ => none
  | .ask i _ => some i
  | .spawn _ _ => none

def stepAsk : BS I A X → A → BS I A X
  | .ask _ k, a => k a
  | s, _ => s

def bfollow (g : X → List A → C) :
    List (I × A) → BS I A X → List (I × Option A) → Table I A → Option C
  | [], own, pend, _ => finished g (pushSpawns own pend).1 (pushSpawns own pend).2
  | (l, a) :: rest, own, pend, t =>
    match finished g (pushSpawns own pend).1 (pushSpawns own pend).2 with
    | some c => some c
    | none =>
      if ownCell (pushSpawns own pend).1 = some l then
        (if waits l (pushSpawns own pend).2 then none
         else if t l = none then
           bfollow g rest (stepAsk (pushSpawns own pend).1 a) (pushSpawns own pend).2 (put t l a)
         else none)
      else if waits l (pushSpawns own pend).2 then
        (if t l = none then
           bfollow g rest (pushSpawns own pend).1 (record l a (pushSpawns own pend).2) (put t l a)
         else none)
      else bfollow g rest (pushSpawns own pend).1 (pushSpawns own pend).2 (put t l a)

end Defs

section Law
variable {I A X C : Type} [DecidableEq I] [Inhabited A] [Fintype A]

noncomputable def pmean (f : List A → ℚ) : List (I × Option A) → ℚ
  | [] => f []
  | (_, some b) :: rest => pmean (fun as => f (b :: as)) rest
  | (_, none) :: rest => mean (fun a => pmean (fun as => f (a :: as)) rest)

noncomputable def blaw (g : X → List A → C) (obs : C → ℚ) :
    BS I A X → List (I × Option A) → ℚ
  | .done x, pend => pmean (fun as => obs (g x as)) pend
  | .ask _ k, pend => mean (fun a => blaw g obs (k a) pend)
  | .spawn c nxt, pend => blaw g obs nxt (pend ++ [(c, none)])

theorem blaw_push (g : X → List A → C) (obs : C → ℚ) :
    ∀ (own : BS I A X) (pend : List (I × Option A)),
      blaw g obs own pend = blaw g obs (pushSpawns own pend).1 (pushSpawns own pend).2 := by
  intro own
  induction own with
  | done x => intro pend; rfl
  | ask i k _ => intro pend; rfl
  | spawn c nxt ih =>
      intro pend
      simp only [blaw, pushSpawns]
      exact ih _

omit [DecidableEq I] [Inhabited A] in
theorem pmean_nonneg : ∀ (pend : List (I × Option A)) (f : List A → ℚ),
    (∀ as, 0 ≤ f as) → 0 ≤ pmean f pend := by
  intro pend
  induction pend with
  | nil => intro f h; exact h []
  | cons p rest ih =>
      intro f h
      obtain ⟨c, o⟩ := p
      cases o with
      | some b => exact ih _ fun as => h _
      | none => exact mean_nonneg fun a => ih _ fun as => h _

omit [DecidableEq I] [Inhabited A] in
theorem blaw_nonneg (g : X → List A → C) (obs : C → ℚ) (hobs : ∀ c, 0 ≤ obs c) :
    ∀ (own : BS I A X) (pend : List (I × Option A)), 0 ≤ blaw g obs own pend := by
  intro own
  induction own with
  | done x => intro pend; exact pmean_nonneg pend _ fun as => hobs _
  | ask i k ih => intro pend; exact mean_nonneg fun a => ih a pend
  | spawn c nxt ih => intro pend; exact ih _

omit [DecidableEq I] [Fintype A] in
theorem answers_cons_some (c : I) (b : A) (rest : List (I × Option A)) :
    answers ((c, some b) :: rest) = b :: answers rest := rfl

omit [DecidableEq I] in
theorem pmean_allDone : ∀ (pend : List (I × Option A)) (f : List A → ℚ),
    allDone pend = true → pmean f pend = f (answers pend) := by
  intro pend
  induction pend with
  | nil => intro f _; rfl
  | cons p rest ih =>
      intro f h
      obtain ⟨c, o⟩ := p
      cases o with
      | none => simp [allDone] at h
      | some b =>
          simp only [pmean, answers_cons_some]
          exact ih _ h

theorem pmean_record (l : I) : ∀ (pend : List (I × Option A)) (f : List A → ℚ),
    waits l pend = true → mean (fun a => pmean f (record l a pend)) = pmean f pend := by
  intro pend
  induction pend with
  | nil => intro f h; simp [waits] at h
  | cons p rest ih =>
      intro f h
      obtain ⟨c, o⟩ := p
      cases o with
      | some b =>
          simp only [waits] at h
          simp only [record, pmean]
          exact ih _ h
      | none =>
          by_cases hc : c = l
          · simp only [record, if_pos hc, pmean]
          · have h' : waits l rest = true := by
              simpa [waits, hc] using h
            simp only [record, if_neg hc, pmean]
            rw [mean_comm]
            apply mean_congr
            intro b
            exact ih _ h'

theorem record_append (l : I) (a : A) : ∀ (pend post : List (I × Option A)),
    waits l pend = true → record l a (pend ++ post) = record l a pend ++ post := by
  intro pend
  induction pend with
  | nil => intro post h; simp [waits] at h
  | cons p rest ih =>
      intro post h
      obtain ⟨c, o⟩ := p
      cases o with
      | some b =>
          simp only [waits] at h
          simp only [List.cons_append, record, ih post h]
      | none =>
          by_cases hc : c = l
          · simp only [List.cons_append, record, if_pos hc]
          · have h' : waits l rest = true := by simpa [waits, hc] using h
            simp only [List.cons_append, record, if_neg hc, ih post h']

theorem waits_append (l : I) : ∀ (pend post : List (I × Option A)),
    waits l pend = true → waits l (pend ++ post) = true := by
  intro pend
  induction pend with
  | nil => intro post h; simp [waits] at h
  | cons p rest ih =>
      intro post h
      obtain ⟨c, o⟩ := p
      cases o with
      | some b => simp only [waits] at h; simp only [List.cons_append, waits]; exact ih post h
      | none =>
          simp only [waits, Bool.or_eq_true] at h
          simp only [List.cons_append, waits, Bool.or_eq_true]
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (ih post h)

theorem blaw_record (g : X → List A → C) (obs : C → ℚ) (l : I) :
    ∀ (own : BS I A X) (pend : List (I × Option A)), waits l pend = true →
      mean (fun a => blaw g obs own (record l a pend)) = blaw g obs own pend := by
  intro own
  induction own with
  | done x => intro pend h; exact pmean_record l pend _ h
  | ask i k ih =>
      intro pend h
      simp only [blaw]
      rw [mean_comm]
      exact mean_congr fun b => ih b pend h
  | spawn c nxt ih =>
      intro pend h
      simp only [blaw]
      have e : ∀ a, record l a pend ++ [(c, none)] = record l a (pend ++ [(c, none)]) :=
        fun a => (record_append l a pend _ h).symm
      simp only [e]
      exact ih _ (waits_append l pend _ h)

omit [DecidableEq I] [Inhabited A] [Fintype A] in
theorem ownCell_some (own : BS I A X) (l : I) (h : ownCell own = some l) :
    ∃ k, own = .ask l k := by
  cases own with
  | done x => simp [ownCell] at h
  | ask i k =>
      simp only [ownCell, Option.some.injEq] at h
      exact ⟨k, by rw [h]⟩
  | spawn c n => simp [ownCell] at h

omit [Fintype A] in
theorem finished_some (g : X → List A → C) (own : BS I A X) (pend : List (I × Option A))
    (c : C) (h : finished g own pend = some c) :
    ∃ x, own = .done x ∧ allDone pend = true ∧ c = g x (answers pend) := by
  cases own with
  | done x =>
      simp only [finished] at h
      split at h
      · rename_i hd
        exact ⟨x, rfl, hd, (Option.some.inj h).symm⟩
      · cases h
  | ask i k => simp [finished] at h
  | spawn c' n => simp [finished] at h

theorem blaw_finished (g : X → List A → C) (obs : C → ℚ) (own : BS I A X)
    (pend : List (I × Option A)) (c : C) (h : finished g own pend = some c) :
    blaw g obs own pend = obs c := by
  obtain ⟨x, rfl, hd, rfl⟩ := finished_some g own pend c h
  exact pmean_allDone pend _ hd

end Law

/-! ## The chain lemma -/

theorem chainB {I A X C O : Type} [DecidableEq I] [Inhabited A] [Fintype A] [Nonempty A]
    (g : X → List A → C) (bad : C → Prop) (q : Program I A O) :
    ∀ (t : Table I A) (own : BS I A X) (pend : List (I × Option A)),
      lazyMean q t (fun v => indicator (∃ c, bfollow g v.1 own pend t = some c ∧ bad c)) ≤
        blaw g (fun c => indicator (bad c)) own pend := by
  have hobs : ∀ c, 0 ≤ indicator (bad c) := fun c => indicator_nonneg _
  induction q with
  | done o =>
      intro t own pend
      change indicator (∃ c, bfollow g [] own pend t = some c ∧ bad c) ≤ _
      rw [blaw_push]
      simp only [bfollow]
      cases hf : finished g (pushSpawns own pend).1 (pushSpawns own pend).2 with
      | none =>
          rw [indicator_iff (q := False) (by simp), indicator_false]
          exact blaw_nonneg g _ hobs _ _
      | some c =>
          rw [blaw_finished g _ _ _ c hf]
          exact indicator_mono fun ⟨c', hc', hb⟩ => by
            cases hc'; exact hb
  | ask i next ih =>
      intro t own pend
      rw [blaw_push]
      set own' := (pushSpawns own pend).1 with hown'
      set pend' := (pushSpawns own pend).2 with hpend'
      have hunf : ∀ (a : A) (r : List (I × A)) (t0 : Table I A),
          bfollow g ((i, a) :: r) own pend t0 =
            match finished g own' pend' with
            | some c => some c
            | none =>
              if ownCell own' = some i then
                (if waits i pend' then none
                 else if t0 i = none then bfollow g r (stepAsk own' a) pend' (put t0 i a)
                 else none)
              else if waits i pend' then
                (if t0 i = none then bfollow g r own' (record i a pend') (put t0 i a) else none)
              else bfollow g r own' pend' (put t0 i a) := by
        intro a r t0; rfl
      cases hf : finished g own' pend' with
      | some c =>
          have hconst : ∀ (a : A) (r : List (I × A)) (t0 : Table I A),
              indicator (∃ c', bfollow g ((i, a) :: r) own pend t0 = some c' ∧ bad c') =
                indicator (bad c) := by
            intro a r t0
            rw [hunf, hf]
            apply indicator_iff
            exact ⟨fun ⟨c', h1, h2⟩ => by cases h1; exact h2, fun h => ⟨c, rfl, h⟩⟩
          rw [blaw_finished g _ _ _ c hf]
          cases ht : t i with
          | some a =>
              simp only [lazyMean, ht]
              rw [lazyMean_congr _ _ (fun v => hconst a v.1 t), lazyMean_const]
          | none =>
              simp only [lazyMean, ht]
              rw [mean_congr (fun a => (lazyMean_congr _ _ (fun v => hconst a v.1 t)).trans
                (lazyMean_const _ _ _)), mean_const]
      | none =>
          cases ht : t i with
          | some a =>
              simp only [lazyMean, ht]
              by_cases ho : ownCell own' = some i
              · have hz : ∀ v : View I A O,
                    indicator (∃ c, bfollow g ((i, a) :: v.1) own pend t = some c ∧ bad c) = 0 := by
                  intro v
                  rw [hunf, hf]
                  simp only [ho, if_true, ht]
                  rw [indicator_iff (q := False) (by split <;> simp), indicator_false]
                rw [lazyMean_congr _ _ hz, lazyMean_const]
                exact blaw_nonneg g _ hobs _ _
              · by_cases hw : waits i pend' = true
                · have hz : ∀ v : View I A O,
                      indicator (∃ c, bfollow g ((i, a) :: v.1) own pend t = some c ∧ bad c) = 0 := by
                    intro v
                    rw [hunf, hf]
                    simp only [ho, if_false, hw, if_true, ht]
                    rw [indicator_iff (q := False) (by simp), indicator_false]
                  rw [lazyMean_congr _ _ hz, lazyMean_const]
                  exact blaw_nonneg g _ hobs _ _
                · have he : ∀ v : View I A O,
                      indicator (∃ c, bfollow g ((i, a) :: v.1) own pend t = some c ∧ bad c) =
                        indicator (∃ c, bfollow g v.1 own' pend' t = some c ∧ bad c) := by
                    intro v
                    rw [hunf, hf]
                    simp only [ho, if_false, hw, Bool.false_eq_true, put_self t i a ht]
                  rw [lazyMean_congr _ _ he]
                  exact ih a t own' pend'
          | none =>
              simp only [lazyMean, ht]
              by_cases ho : ownCell own' = some i
              · obtain ⟨k, hk⟩ := ownCell_some own' i ho
                by_cases hw : waits i pend' = true
                · have hz : ∀ (a : A) (v : View I A O),
                      indicator (∃ c, bfollow g ((i, a) :: v.1) own pend t = some c ∧ bad c) = 0 := by
                    intro a v
                    rw [hunf, hf]
                    simp only [ho, if_true, hw]
                    rw [indicator_iff (q := False) (by simp), indicator_false]
                  rw [mean_congr (fun a => (lazyMean_congr _ _ (hz a)).trans (lazyMean_const _ _ _)),
                    mean_const]
                  exact blaw_nonneg g _ hobs _ _
                · have he : ∀ (a : A) (v : View I A O),
                      indicator (∃ c, bfollow g ((i, a) :: v.1) own pend t = some c ∧ bad c) =
                        indicator (∃ c, bfollow g v.1 (k a) pend' (put t i a) = some c ∧ bad c) := by
                    intro a v
                    rw [hunf, hf]
                    simp only [ho, if_true, hw, Bool.false_eq_true, if_false, ht]
                    rw [hk]
                    rfl
                  rw [hk]
                  simp only [blaw]
                  apply mean_mono
                  intro a
                  rw [lazyMean_congr _ _ (he a)]
                  exact ih a (put t i a) (k a) pend'
              · by_cases hw : waits i pend' = true
                · have he : ∀ (a : A) (v : View I A O),
                      indicator (∃ c, bfollow g ((i, a) :: v.1) own pend t = some c ∧ bad c) =
                        indicator (∃ c, bfollow g v.1 own' (record i a pend') (put t i a) = some c ∧
                          bad c) := by
                    intro a v
                    rw [hunf, hf]
                    simp only [ho, if_false, hw, if_true, ht]
                  rw [← blaw_record g _ i own' pend' hw]
                  apply mean_mono
                  intro a
                  rw [lazyMean_congr _ _ (he a)]
                  exact ih a (put t i a) own' (record i a pend')
                · have he : ∀ (a : A) (v : View I A O),
                      indicator (∃ c, bfollow g ((i, a) :: v.1) own pend t = some c ∧ bad c) =
                        indicator (∃ c, bfollow g v.1 own' pend' (put t i a) = some c ∧ bad c) := by
                    intro a v
                    rw [hunf, hf]
                    simp only [ho, if_false, hw, Bool.false_eq_true]
                  calc mean (fun a => lazyMean (next a) (put t i a)
                        (fun r => indicator (∃ c, bfollow g ((i, a) :: r.1) own pend t = some c ∧ bad c)))
                      ≤ mean (fun _ : A => blaw g (fun c => indicator (bad c)) own' pend') := by
                        apply mean_mono
                        intro a
                        rw [lazyMean_congr _ _ (he a)]
                        exact ih a (put t i a) own' pend'
                    _ = _ := mean_const _

#print axioms chainB
end R0C.V3
