import FS2.LemmaA
import FS.LemmaB

/-! # Lemma B′ and the v2 theorem

Lemma B′: outside the collision event, acceptance with a failed extractor
yields a first round where doomedness flips; that round's chain starts at a
first read whose address decodes to a completing sampler that is followed to
the round's prefix, message and challenge (INJ), so the first read is in
`hitsChain` with the (D2′) bad family.

Composition: as v1, with Lemma A′ charging `max_i ε_i` per first read.

`follow_consistent` (not needed by the generic proof; used by instantiations
to discharge (INJ)): a followed sampler on a consistent trace outputs the
oracle run's result. -/
set_option autoImplicit false
namespace FS2

open FS AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment

section Follow
variable {I A C : Type} [DecidableEq I] [Inhabited A]

/-- The answers of a list of cells, on top of a base assignment. -/
def accOf (H : I → A) : List I → (I → A) → (I → A)
  | [], base => base
  | c :: cs, base => Function.update (accOf H cs base) c (H c)

theorem accOf_apply (H : I → A) : ∀ (cells : List I) (base : I → A) (i : I),
    accOf H cells base i = if i ∈ cells then H i else base i := by
  intro cells
  induction cells with
  | nil => intro base i; simp [accOf]
  | cons c cs ih =>
      intro base i
      simp only [accOf, List.mem_cons]
      by_cases hic : i = c
      · subst hic; simp
      · simp [Function.update_of_ne hic, ih, hic]

theorem eval_multiProg (H : I → A) : ∀ (cells : List I) (f : (I → A) → Program I A C),
    (eval H (multiProg cells f)).2 = (eval H (f (accOf H cells default))).2 := by
  intro cells
  induction cells with
  | nil => intro f; rfl
  | cons c cs ih =>
      intro f
      simp only [multiProg, eval]
      exact ih (fun acc => f (Function.update acc c (H c)))

/-- Consuming any member cell of a `multi` with its oracle value does not
change the run's output. -/
theorem eval_stepMulti (H : I → A) (c : I) (cs : List I) (nd : (c :: cs).Nodup)
    (k : (I → A) → Sampler I A C) (l : I) (hl : l ∈ c :: cs) :
    (eval H (stepMulti c cs nd k l (H l)).toProgram).2 =
      (eval H (Sampler.multi c cs nd k).toProgram).2 := by
  have hacc : ∀ cells : List I, Function.update (accOf H ((c :: cs).erase l) default) l (H l) =
      accOf H (c :: cs) default := by
    intro _
    funext i
    by_cases hil : i = l
    · subst hil; simp [accOf_apply, hl]
    · rw [Function.update_of_ne hil, accOf_apply, accOf_apply]
      have : i ∈ (c :: cs).erase l ↔ i ∈ c :: cs := by
        constructor
        · exact List.mem_of_mem_erase
        · intro h; exact (List.mem_erase_of_ne hil).mpr h
      simp only [this]
  unfold stepMulti
  split
  · rename_i h
    simp only [Sampler.toProgram, eval_multiProg]
    have := hacc []
    rw [h, accOf] at this
    rw [this]
  · rename_i c' cs' h
    simp only [Sampler.toProgram, eval_multiProg]
    have := hacc []
    rw [h] at this
    rw [this]

/-- A followed sampler on a consistent trace outputs the oracle run's result. -/
theorem follow_consistent (H : I → A) :
    ∀ (tr : List (I × A)) (s : Sampler I A C) (t : Table I A) (c : C),
      (∀ q ∈ tr, q.2 = H q.1) → follow s t tr = some c → c = (eval H s.toProgram).2 := by
  intro tr
  induction tr with
  | nil =>
      intro s t c _ h
      cases s with
      | done c' => simp [follow] at h; rw [h]; rfl
      | ask i k => simp [follow] at h
      | multi c cs nd k => simp [follow] at h
  | cons q rest ih =>
      intro s t c hcons h
      obtain ⟨l, a⟩ := q
      have hrest : ∀ q ∈ rest, q.2 = H q.1 := fun q hq => hcons q (List.mem_cons_of_mem _ hq)
      have ha : a = H l := hcons (l, a) (List.mem_cons_self ..)
      cases s with
      | done c' => simp [follow] at h; rw [h]; rfl
      | ask i k =>
          simp only [follow] at h
          by_cases hli : l = i
          · subst hli
            simp only [if_true] at h
            split at h
            · rw [ih (k a) (put t l a) c hrest h, ha]
              rfl
            · cases h
          · simp only [hli, if_false] at h
            exact ih _ _ c hrest h
      | multi c0 cs nd k =>
          simp only [follow] at h
          by_cases hmem : l ∈ c0 :: cs
          · simp only [hmem, if_true] at h
            split at h
            · rw [ih _ (put t l a) c hrest h, ha, eval_stepMulti H c0 cs nd k l hmem]
            · cases h
          · simp only [hmem, if_false] at h
            exact ih _ _ c hrest h

end Follow

section Chain
variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A]

theorem transcript_round (pr : Protocol X M C W Pf I A) (H : I → A) (x : X) (π : Pf) :
    ∀ n, (pr.transcript H x π n).round = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Protocol.transcript, Prefix.ext, Prefix.round, List.length_append,
        List.length_singleton]
      exact congrArg (· + 1) ih

theorem mem_traceFrom (a : I) :
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

/-- A first read of `a` whose decoded sampler is followed to a bad output from
the table before it puts the trace in `hitsChain`. -/
theorem hitsChain_of_first (bad : Prefix X M C → M → Table I A → C → Prop)
    (pr : Protocol X M C W Pf I A) (a : I) :
    ∀ (tr : List (I × A)) (t : Table I A),
      a ∈ tr.map Prod.fst → t a = none →
      (∃ (S : Sampler I A (Prefix X M C × M × C)) (P : Prefix X M C) (m : M) (c : C),
        pr.decode a (tableBefore t tr a) = some S ∧
        follow S (tableBefore t tr a) (traceFrom tr a) = some (P, m, c) ∧
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
variable {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A] [Fintype I] [Fintype A] [Nonempty A]

omit [DecidableEq I] [Inhabited A] [Fintype I] [Fintype A] [Nonempty A] in
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

omit [Nonempty A] in
theorem lemmaB (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : LemmaB pr rb P V x κ Qtot := by
  intro hD1 hD3 hreads hV inj H hcoll hacc hfail
  set v := eval H (experiment P V x) with hv
  have hπ : v.2.1 = (eval H P).2 := by rw [hv, experiment_eval]
  set π := (eval H P).2 with hπdef
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
  obtain ⟨S, hS, hf⟩ := hdec ha
  apply hitsChain_of_first (d2Bad pr rb) pr a v.1 emptyTable hmem rfl
  refine ⟨S, pr.transcript H x π i, pr.msg π i, pr.chal H x π i, hS, hf, ?_⟩
  refine ⟨by rw [transcript_round]; exact hi, hdoomed, ?_⟩
  rw [← hT]
  exact hnot'

theorem theorem4 (pr : Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : Theorem4 pr rb P V x κ Qtot := by
  intro hD1 hCD hD3 hreads hV inj hQ
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
    · exact Or.inr (lemmaB pr rb P V x κ Qtot hD1 hD3 hreads hV inj H hc hacc hfail)
  have hA : mean (fun H : I → A =>
      indicator (hitsChain (d2Bad pr rb) pr emptyTable (eval H exp).1)) ≤
        (Qtot : ℚ) * maxErr rb.ε pr.r := by
    rw [empty_oracle_law exp (fun v => indicator (hitsChain (d2Bad pr rb) pr emptyTable v.1))]
    apply lemmaA pr (d2Bad pr rb) (maxErr rb.ε pr.r) exp emptyTable Qtot (maxErr_nonneg _ _)
      (fun a T S h => hCD a T S h)
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

#print axioms follow_consistent
#print axioms lemmaB
#print axioms theorem4
end Main
end FS2
