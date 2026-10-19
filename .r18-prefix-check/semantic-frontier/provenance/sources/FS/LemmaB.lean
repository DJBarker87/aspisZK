import FS.Statement

/-! # Lemma B: deterministic inclusion

Outside the collision event, if `V` accepts and the extractor fails, the first
round at which doomedness flips puts the fresh block at that round's address
into the (D2) bad set, at the table of that address's first read. -/
set_option autoImplicit false
namespace FS

open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8PairedCommitment

/-- First round where a predicate flips from true to false. -/
theorem exists_flip (e : Nat → Prop) : ∀ r, e 0 → ¬ e r → ∃ i, i < r ∧ e i ∧ ¬ e (i + 1) := by
  intro r
  induction r with
  | zero => intro h0 hr; exact absurd h0 hr
  | succ r ih =>
      intro h0 hr
      by_cases hre : e r
      · exact ⟨r, Nat.lt_succ_self r, hre, hr⟩
      · obtain ⟨i, hi, hei, hnot⟩ := ih h0 hre
        exact ⟨i, Nat.lt_succ_of_lt hi, hei, hnot⟩

section Trace
variable {I A O : Type} [DecidableEq I]

omit [DecidableEq I] in
/-- Every trace entry of a complete-oracle run carries the oracle's value. -/
theorem eval_consistent (H : I → A) (p : Program I A O) :
    ∀ q ∈ (eval H p).1, q.2 = H q.1 := by
  induction p with
  | done o => intro q hq; simp [eval] at hq
  | ask i next ih =>
      intro q hq
      simp only [eval, List.mem_cons] at hq
      rcases hq with rfl | hq
      · rfl
      · exact ih (H i) q hq

/-- If `j` is read in a consistent trace started at a table lacking `j`, and
the bad set at the table before its first read contains the oracle's answer,
the trace hits a bad set. -/
theorem hitsBad_of_first (bad : I → Table I A → A → Prop) (H : I → A) (j : I) :
    ∀ (tr : List (I × A)) (t : Table I A), (∀ q ∈ tr, q.2 = H q.1) →
      j ∈ tr.map Prod.fst → t j = none → bad j (tableBefore t tr j) (H j) →
      hitsBad bad t tr := by
  intro tr
  induction tr with
  | nil => intro t _ hj; simp at hj
  | cons q rest ih =>
      intro t hcons hj hnone hbad
      obtain ⟨i, a⟩ := q
      have ha : a = H i := hcons (i, a) (List.mem_cons_self ..)
      by_cases hij : i = j
      · subst hij
        simp only [tableBefore, if_true] at hbad
        exact Or.inl ⟨hnone, ha ▸ hbad⟩
      · simp only [tableBefore, hij, if_false] at hbad
        refine Or.inr (ih (put t i a) (fun q hq => hcons q (List.mem_cons_of_mem _ hq)) ?_ ?_ hbad)
        · simp only [List.map_cons, List.mem_cons] at hj
          rcases hj with h | h
          · exact absurd h.symm hij
          · exact h
        · simp [put, Ne.symm hij, hnone]

end Trace

section Exp
variable {X M C W Pf I B : Type} {K : Nat} [DecidableEq I]

omit [DecidableEq I] in
theorem experiment_eval (P : Program I (Block B K) Pf) (V : X → Pf → Program I (Block B K) Bool)
    (x : X) (H : I → Block B K) :
    eval H (experiment P V x) =
      ((eval H P).1 ++ (eval H (V x (eval H P).2)).1,
        ((eval H P).2, (eval H (V x (eval H P).2)).2)) := by
  unfold experiment
  rw [eval_bind]
  dsimp only
  rw [eval_bind]
  dsimp only
  simp [eval]

end Exp

theorem transcript_round {X M C W Pf I B : Type} {K : Nat}
    (pr : Protocol X M C W Pf I B K) (H : I → Block B K) (x : X) (π : Pf) :
    ∀ n, (pr.transcript H x π n).round = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Protocol.transcript, Prefix.ext, Prefix.round, List.length_append,
        List.length_singleton]
      exact congrArg (· + 1) ih

section Main
variable {X M C W Pf I B : Type} {K : Nat} [DecidableEq I] [Fintype I] [Fintype B]

/-- Lemma B. -/
theorem lemmaB (pr : Protocol X M C W Pf I B K) (rb : RoundByRound X M C I B K)
    (P : Program I (Block B K) Pf) (V : X → Pf → Program I (Block B K) Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) : LemmaB pr rb P V x κ Qtot := by
  intro hD1 hD3 hV inj H hcoll hacc hfail
  set v := eval H (experiment P V x) with hv
  have hπ : v.2.1 = (eval H P).2 := by rw [hv, experiment_eval]
  set π := (eval H P).2 with hπdef
  -- the chain of transcript prefixes, each at the table of its own first read
  let T : Nat → Table I (Block B K) := fun i =>
    tableBefore emptyTable v.1 (pr.chalAddr H x π i)
  let e : Nat → Prop := fun i => rb.doomed (pr.transcript H x π i)
    (if i = 0 then T 0 else T (i - 1))
  have e0 : e 0 := by
    simp only [e, if_true, T, Protocol.chalAddr, Protocol.transcript]
    apply hD1
    simpa [extractFails, hπ] using hfail
  have er : ¬ e pr.r := by
    intro hr
    have hrej := hD3 H x π _ hr
    have : v.2.2 = (eval H (V x π)).2 := by rw [hv, experiment_eval]
    simp only [accepts] at hacc
    rw [this] at hacc
    rw [hacc] at hrej
    simp at hrej
  obtain ⟨i, hi, hei, hnot⟩ := exists_flip e pr.r e0 er
  -- the flip: round i doomed (at some table), round i+1 not doomed at T i
  have hnot' : ¬ rb.doomed (pr.transcript H x π (i + 1)) (T i) := by
    simpa [e] using hnot
  have hdoomed : ∃ T', rb.doomed (pr.transcript H x π i) T' := ⟨_, hei⟩
  -- the address of round i is read by the verifier, hence in the trace
  have hmem : pr.chalAddr H x π i ∈ v.1.map Prod.fst := by
    have := hV H x π i hi
    rw [hv, experiment_eval, List.map_append, List.mem_append]
    exact Or.inr this
  have hdec := inj.decodes H hcoll i hi
  dsimp only at hdec
  rw [hπ] at hdec
  apply hitsBad_of_first (d2Bad pr rb) H (pr.chalAddr H x π i) v.1 emptyTable
    (eval_consistent H _) hmem rfl
  refine ⟨pr.transcript H x π i, pr.msg π i, hdec, ?_, hdoomed, ?_⟩
  · rw [transcript_round]; exact hi
  · rw [transcript_round]
    exact hnot'

#print axioms lemmaB
end Main
end FS
