import FS2.LemmaA
import FS.LemmaB

/-! # Lemma B′ and the v2 theorem

Lemma B′: outside the collision event, acceptance with a failed extractor
yields a first round where doomedness flips; that round's chain starts at a
first read whose address decodes to the round (INJ), the chain is followed to
completion from there (INJ), and its output is the transcript's challenge, so
the first read is in `hitsChain` with the (D2′) bad family.

Composition: as v1, with Lemma A′ charging `max_i ε_i` per first read. -/
set_option autoImplicit false
namespace FS2

open FS AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment

section Follow
variable {I A C : Type} [DecidableEq I]

/-- A followed chain on a consistent trace outputs the oracle run's result. -/
theorem follow_consistent (H : I → A) :
    ∀ (tr : List (I × A)) (s : Program I A C) (t : Table I A) (c : C),
      (∀ q ∈ tr, q.2 = H q.1) → follow s t tr = some c → c = (eval H s).2 := by
  intro tr
  induction tr with
  | nil =>
      intro s t c _ h
      cases s with
      | done c' => simp [follow] at h; rw [h]; rfl
      | ask i k => simp [follow] at h
  | cons q rest ih =>
      intro s t c hcons h
      obtain ⟨j, a⟩ := q
      cases s with
      | done c' => simp [follow] at h; rw [h]; rfl
      | ask i k =>
          simp only [follow] at h
          by_cases hji : j = i
          · subst hji
            simp only [if_true] at h
            split at h
            · have ha : a = H j := hcons (j, a) (List.mem_cons_self ..)
              rw [ih (k a) (put t j a) c (fun q hq => hcons q (List.mem_cons_of_mem _ hq)) h, ha]
              rfl
            · cases h
          · simp only [hji, if_false] at h
            exact ih _ _ c (fun q hq => hcons q (List.mem_cons_of_mem _ hq)) h

end Follow

section Chain
variable {X M C W Pf I A : Type} [DecidableEq I]

omit [DecidableEq I] in
theorem transcript_round (pr : Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) :
    ∀ n, (pr.transcript H x π n).round = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Protocol.transcript, Prefix.ext, Prefix.round, List.length_append,
        List.length_singleton]
      exact congrArg (· + 1) ih

/-- A first read of `a` whose decoded chain is followed to a bad output from
the table before it puts the trace in `hitsChain`. -/
theorem hitsChain_of_first (bad : Prefix X M C → M → Table I A → C → Prop)
    (pr : Protocol X M C W Pf I A) (a : I) :
    ∀ (tr : List (I × A)) (t : Table I A),
      a ∈ tr.map Prod.fst → t a = none →
      (∃ (P : Prefix X M C) (m : M) (c : C), pr.decode a (tableBefore t tr a) = some (P, m) ∧
        follow (pr.samp P.round P m) (tableBefore t tr a) (traceFrom tr a) = some c ∧
        bad P m (tableBefore t tr a) c) →
      hitsChain bad pr t tr := by
  intro tr
  induction tr with
  | nil => intro t h; simp at h
  | cons q rest ih =>
      intro t hmem hnone hbad
      obtain ⟨i, b⟩ := q
      by_cases hia : i = a
      · subst hia
        simp only [tableBefore, traceFrom, if_true] at hbad
        exact Or.inl ⟨hnone, hbad⟩
      · simp only [tableBefore, traceFrom, hia, if_false] at hbad
        refine Or.inr (ih (put t i b) ?_ ?_ hbad)
        · simp only [List.map_cons, List.mem_cons] at hmem
          rcases hmem with h | h
          · exact absurd h.symm hia
          · exact h
        · simp [put, Ne.symm hia, hnone]

end Chain

section Main
variable {X M C W Pf I A : Type} [DecidableEq I] [Fintype I] [Fintype A] [Nonempty A]

omit [DecidableEq I] [Fintype I] [Fintype A] [Nonempty A] in
theorem experiment_eval (P : Program I A Pf) (V : X → Pf → Program I A Bool)
    (x : X) (H : I → A) :
    eval H (experiment P V x) =
      ((eval H P).1 ++ (eval H (V x (eval H P).2)).1,
        ((eval H P).2, (eval H (V x (eval H P).2)).2)) := by
  unfold experiment
  rw [eval_bind]
  dsimp only
  rw [eval_bind]
  dsimp only
  simp [eval]

theorem mem_traceFrom {I A : Type} [DecidableEq I] (a : I) :
    ∀ (tr : List (I × A)) (q : I × A), q ∈ traceFrom tr a → q ∈ tr := by
  intro tr
  induction tr with
  | nil => intro q h; simp [traceFrom] at h
  | cons p rest ih =>
      intro q h
      obtain ⟨i, b⟩ := p
      simp only [traceFrom] at h
      split at h
      · exact h
      · exact List.mem_cons_of_mem _ (ih q h)

omit [Nonempty A] in
theorem lemmaB (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : LemmaB pr rb P V x κ Qtot := by
  intro hD1 _ hD3 hreads hV inj H hcoll hacc hfail
  set v := eval H (experiment P V x) with hv
  have hπ : v.2.1 = (eval H P).2 := by rw [hv, experiment_eval]
  set π := (eval H P).2 with hπdef
  have hcons : ∀ q ∈ v.1, q.2 = H q.1 := FS.eval_consistent H _
  classical
  -- the table at the first read of round i's first cell
  let T : Nat → Table I A := fun i =>
    match firstCell (pr.chain H x π i) with
    | some a => tableBefore emptyTable v.1 a
    | none => emptyTable
  let e : Nat → Prop := fun i =>
    rb.doomed (pr.transcript H x π i) (if i = 0 then T 0 else T (i - 1))
  have e0 : e 0 := by
    simp only [e, if_true]
    apply hD1
    simp only [extractFails, hπ] at hfail
    simp only [T, Protocol.chain, Protocol.transcript]
    cases h : firstCell (pr.samp 0 (emptyPrefix x) (pr.msg π 0)) <;>
      simp only [h] at hfail ⊢ <;> exact hfail
  have er : ¬ e pr.r := by
    intro hr
    have hrej := hD3 H x π _ hr
    have : v.2.2 = (eval H (V x π)).2 := by rw [hv, experiment_eval]
    simp only [accepts] at hacc
    rw [this] at hacc
    rw [hacc] at hrej
    simp at hrej
  obtain ⟨i, hi, hei, hnot⟩ := FS.exists_flip e pr.r e0 er
  have hnot' : ¬ rb.doomed (pr.transcript H x π (i + 1)) (T i) := by
    simpa [e] using hnot
  have hdoomed : ∃ T', rb.doomed (pr.transcript H x π i) T' := ⟨_, hei⟩
  -- the chain of round i starts at a first-read cell
  have hne := hreads i (pr.transcript H x π i) (pr.msg π i) hi
  obtain ⟨a, ha⟩ : ∃ a, firstCell (pr.chain H x π i) = some a := by
    cases h : firstCell (pr.chain H x π i) with
    | none => exact absurd h hne
    | some a => exact ⟨a, rfl⟩
  have hT : T i = tableBefore emptyTable v.1 a := by simp [T, ha]
  have hmem : a ∈ v.1.map Prod.fst := by
    have := hV H x π i a hi ha
    rw [hv, experiment_eval, List.map_append, List.mem_append]
    exact Or.inr this
  have hdec := inj.decodes H hcoll i a hi
  dsimp only at hdec
  rw [hπ] at hdec
  have hdec := hdec ha
  have hfol := inj.followed H hcoll i a hi
  dsimp only at hfol
  rw [hπ] at hfol
  obtain ⟨c, hc⟩ := hfol ha
  have hcval : c = (eval H (pr.chain H x π i)).2 :=
    follow_consistent H _ _ _ c (fun q hq => hcons q (mem_traceFrom a v.1 q hq)) hc
  apply hitsChain_of_first (d2Bad pr rb) pr a v.1 emptyTable hmem rfl
  refine ⟨pr.transcript H x π i, pr.msg π i, c, hdec, ?_, ?_⟩
  · rw [transcript_round]
    exact hc
  · refine ⟨by rw [transcript_round]; exact hi, hdoomed, ?_⟩
    rw [← hT, hcval]
    exact hnot'

/-! ## Composition -/

omit [DecidableEq I] [Fintype I] in
theorem independentMean_const (s : Program I A C) (c : ℚ) :
    independentMean s (fun _ => c) = c := by
  induction s with
  | done _ => rfl
  | ask i k ih =>
      simp only [independentMean]
      rw [mean_congr fun a => ih a]
      exact mean_const c

theorem d2Bad_density (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (hD2 : D2 pr rb) (P : Prefix X M C) (m : M) (T : Table I A) :
    independentMean (pr.samp P.round P m) (fun w => indicator (d2Bad pr rb P m T w.2)) ≤
      maxErr rb.ε pr.r := by
  by_cases h : P.round < pr.r ∧ ∃ T', rb.doomed P T'
  · obtain ⟨hr, T', hT'⟩ := h
    calc independentMean (pr.samp P.round P m) (fun w => indicator (d2Bad pr rb P m T w.2))
        = independentMean (pr.samp P.round P m)
            (fun w => indicator (¬ rb.doomed (P.ext m w.2) T)) := by
          apply independentMean_outcome (pr.samp P.round P m)
            (fun c => indicator (¬ rb.doomed (P.ext m c) T))
          intro w
          apply indicator_iff
          simp only [d2Bad]
          exact ⟨fun h => h.2.2, fun h => ⟨hr, ⟨T', hT'⟩, h⟩⟩
      _ ≤ rb.ε P.round := hD2 P.round P m T' T rfl hr hT'
      _ ≤ maxErr rb.ε pr.r := le_maxErr rb.ε pr.r P.round hr
  · have hz : ∀ w : View I A C, indicator (d2Bad pr rb P m T w.2) = 0 := by
      intro w
      rw [indicator_iff (q := False), indicator_false]
      constructor
      · rintro ⟨hr, hT', _⟩; exact h ⟨hr, hT'⟩
      · exact False.elim
    rw [independentMean_outcome _ (fun _ => (0 : ℚ)) _ hz, independentMean_const]
    exact maxErr_nonneg _ _

theorem theorem4 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : Theorem4 pr rb P V x κ Qtot := by
  intro hD1 hD2 hD3 hreads hV inj hQ
  set exp := experiment P V x with hexp
  have hpoint : ∀ H : I → A,
      indicator (accepts (eval H exp) ∧ extractFails pr x (eval H exp)) ≤
        indicator (inj.Coll (eval H exp)) +
          indicator (hitsChain (d2Bad pr rb) pr emptyTable (eval H exp).1) := by
    intro H
    refine le_trans (indicator_mono ?_) (indicator_or_le _ _)
    rintro ⟨hacc, hfail⟩
    by_cases hc : inj.Coll (eval H exp)
    · exact Or.inl hc
    · exact Or.inr (lemmaB pr rb P V x κ Qtot hD1 hD2 hD3 hreads hV inj H hc hacc hfail)
  have hA : mean (fun H : I → A =>
      indicator (hitsChain (d2Bad pr rb) pr emptyTable (eval H exp).1)) ≤
        (Qtot : ℚ) * maxErr rb.ε pr.r := by
    rw [empty_oracle_law exp (fun v => indicator (hitsChain (d2Bad pr rb) pr emptyTable v.1))]
    apply lemmaA pr (d2Bad pr rb) (maxErr rb.ε pr.r) exp emptyTable Qtot (maxErr_nonneg _ _)
      (fun P m T => d2Bad_density pr rb hD2 P m T)
    apply firstReadsBound_of_traces
    intro H
    have := hQ H
    have hc : complete (emptyTable : Table I A) H = H := rfl
    rw [hc]
    exact this
  calc mean (fun H : I → A =>
          indicator (accepts (eval H exp) ∧ extractFails pr x (eval H exp)))
      ≤ mean (fun H : I → A =>
          indicator (inj.Coll (eval H exp)) +
            indicator (hitsChain (d2Bad pr rb) pr emptyTable (eval H exp).1)) := mean_mono hpoint
    _ = mean (fun H : I → A => indicator (inj.Coll (eval H exp))) +
          mean (fun H : I → A =>
            indicator (hitsChain (d2Bad pr rb) pr emptyTable (eval H exp).1)) := mean_add _ _
    _ ≤ κ Qtot + (Qtot : ℚ) * maxErr rb.ε pr.r := add_le_add inj.mass hA
    _ = (Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot := add_comm _ _

#print axioms lemmaB
#print axioms theorem4
end Main
end FS2
