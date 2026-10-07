import R0C.V3.BS

/-! # Fiat–Shamir v3: decoders returning background-read samplers

Everything except the decoder is FS2's: `FS2.Protocol` (whose own `decode`
field is unused here), transcript, chains, experiment, verifier, (D1), (D3),
`ChainsRead`, `ReadsChains`, `d2Bad`.  The decoder returns a `BS` sampler
with an initial background set and an output function; the per-read charge
is its `blaw`. -/
set_option autoImplicit false
namespace R0C.V3

open FS2 AspisV8R19.MemoizedProgramLaw
open FS (indicator_false indicator_iff indicator_or_le indicator_mono lazyMean_congr lazyMean_const
  lazyMean_mono lazyMean_add mean_mono mean_add put_self maxErr_nonneg firstReadsBound_of_traces
  FirstReadsBound maxErr emptyTable tableBefore firstReads Prefix emptyPrefix)
open AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8PairedCommitment

/-- A v3 decoder: completing sampler, initial background set, output map. -/
abbrev Dec (X M C I A Y : Type) :=
  I → Table I A → Option (BS I A Y × List (I × Option A) × (Y → List A → Prefix X M C × M × C))

section Defs
variable {X M C W Pf I A Y : Type} [DecidableEq I] [Inhabited A]

def hitsChain3 (dec : Dec X M C I A Y) (bad : Prefix X M C → M → Table I A → C → Prop) :
    Table I A → List (I × A) → Prop
  | _, [] => False
  | t, (i, a) :: rest =>
      (t i = none ∧ ∃ own pend g P m c, dec i t = some (own, pend, g) ∧
        bfollow g ((i, a) :: rest) own pend t = some (P, m, c) ∧ bad P m t c) ∨
      hitsChain3 dec bad (put t i a) rest

variable [Fintype A]

def ChainDensity3 (pr : FS2.Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (dec : Dec X M C I A Y) : Prop :=
  ∀ (a : I) (T : Table I A) own pend g, dec a T = some (own, pend, g) →
    blaw g (fun out => indicator (d2Bad pr rb out.1 out.2.1 T out.2.2)) own pend ≤
      maxErr rb.ε pr.r

variable [Fintype I]

structure Inj3 (pr : FS2.Protocol X M C W Pf I A) (dec : Dec X M C I A Y) (P : Program I A Pf)
    (V : X → Pf → Program I A Bool) (x : X) (κ : Nat → ℚ) (Qtot : Nat) where
  Coll : View I A (Pf × Bool) → Prop
  mass : mean (fun H : I → A => indicator (Coll (eval H (experiment P V x)))) ≤ κ Qtot
  decodes : ∀ H : I → A, ¬ Coll (eval H (experiment P V x)) →
    ∀ i a, i < pr.r →
      firstCell (pr.chain H x (eval H (experiment P V x)).2.1 i) = some a →
      ∃ own pend g, dec a (tableBefore emptyTable (eval H (experiment P V x)).1 a) =
          some (own, pend, g) ∧
        bfollow g (traceFrom (eval H (experiment P V x)).1 a) own pend
          (tableBefore emptyTable (eval H (experiment P V x)).1 a) =
          some (pr.transcript H x (eval H (experiment P V x)).2.1 i,
            pr.msg (eval H (experiment P V x)).2.1 i, pr.chal H x (eval H (experiment P V x)).2.1 i)

end Defs

/-! ## Lemma A₃ -/

theorem lemmaA3 {X M C Pf I A Y : Type} [DecidableEq I] [Inhabited A] [Fintype A] [Nonempty A]
    (dec : Dec X M C I A Y) (bad : Prefix X M C → M → Table I A → C → Prop)
    (ε : ℚ) (q : Program I A (Pf × Bool)) (t : Table I A) (N : Nat) (hε : 0 ≤ ε)
    (hbad : ∀ (a : I) (T : Table I A) own pend g, dec a T = some (own, pend, g) →
      blaw g (fun out => indicator (bad out.1 out.2.1 T out.2.2)) own pend ≤ ε)
    (hN : FirstReadsBound q t N) :
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
          simp only [FirstReadsBound, ht] at hN
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
          simp only [FirstReadsBound, ht] at hN
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

/-! ## Lemma B₃ and the theorem -/

section Main
variable {X M C W Pf I A Y : Type} [DecidableEq I] [Inhabited A] [Fintype I] [Fintype A]

omit [Fintype I] [Fintype A] in
theorem hitsChain3_of_first (dec : Dec X M C I A Y) (bad : Prefix X M C → M → Table I A → C → Prop)
    (a : I) : ∀ (tr : List (I × A)) (t : Table I A),
      a ∈ tr.map Prod.fst → t a = none →
      (∃ own pend g P m c, dec a (tableBefore t tr a) = some (own, pend, g) ∧
        bfollow g (traceFrom tr a) own pend (tableBefore t tr a) = some (P, m, c) ∧
        bad P m (tableBefore t tr a) c) →
      hitsChain3 dec bad t tr := by
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

theorem lemmaB3 (pr : FS2.Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (dec : Dec X M C I A Y) (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) (hD1 : FS2.D1 pr rb) (hD3 : FS2.D3 pr rb V)
    (hreads : ChainsRead pr) (hV : ReadsChains pr V) (inj : Inj3 pr dec P V x κ Qtot)
    (H : I → A) (hcoll : ¬ inj.Coll (eval H (experiment P V x)))
    (hacc : accepts (eval H (experiment P V x)))
    (hfail : extractFails pr x (eval H (experiment P V x))) :
    hitsChain3 dec (d2Bad pr rb) emptyTable (eval H (experiment P V x)).1 := by
  set v := eval H (experiment P V x) with hv
  have hπ : v.2.1 = (eval H P).2 := by rw [hv, FS2.experiment_eval]
  set π := (eval H P).2 with hπdef
  classical
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
    have : v.2.2 = (eval H (V x π)).2 := by rw [hv, FS2.experiment_eval]
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
    rw [hv, FS2.experiment_eval, List.map_append, List.mem_append]
    exact Or.inr this
  have hdec := inj.decodes H hcoll i a hi
  rw [← hv, hπ] at hdec
  obtain ⟨own, pend, g, hS, hf⟩ := hdec ha
  apply hitsChain3_of_first dec (d2Bad pr rb) a v.1 emptyTable hmem rfl
  refine ⟨own, pend, g, pr.transcript H x π i, pr.msg π i, pr.chal H x π i, hS, hf, ?_⟩
  refine ⟨by rw [FS2.transcript_round]; exact hi, hdoomed, ?_⟩
  rw [← hT]
  exact hnot'

theorem theorem43 [Nonempty A] (pr : FS2.Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (dec : Dec X M C I A Y) (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) (hD1 : FS2.D1 pr rb) (hCD : ChainDensity3 pr rb dec)
    (hD3 : FS2.D3 pr rb V) (hreads : ChainsRead pr) (hV : ReadsChains pr V)
    (inj : Inj3 pr dec P V x κ Qtot)
    (hQ : ∀ H, distinctFirstReads (eval H (experiment P V x)) ≤ Qtot) :
    mean (fun H : I → A =>
        indicator (accepts (eval H (experiment P V x)) ∧
          extractFails pr x (eval H (experiment P V x)))) ≤
      (Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot := by
  set exp := experiment P V x with hexp
  have hpoint : ∀ H : I → A,
      indicator (accepts (eval H exp) ∧ extractFails pr x (eval H exp)) ≤
        indicator (inj.Coll (eval H exp)) +
          indicator (hitsChain3 dec (d2Bad pr rb) emptyTable (eval H exp).1) := by
    intro H
    refine le_trans (indicator_mono ?_) (indicator_or_le _ _)
    rintro ⟨hacc, hfail⟩
    by_cases hc : inj.Coll (eval H exp)
    · exact Or.inl hc
    · exact Or.inr (lemmaB3 pr rb dec P V x κ Qtot hD1 hD3 hreads hV inj H hc hacc hfail)
  have hA : mean (fun H : I → A =>
      indicator (hitsChain3 dec (d2Bad pr rb) emptyTable (eval H exp).1)) ≤
        (Qtot : ℚ) * maxErr rb.ε pr.r := by
    rw [empty_oracle_law exp (fun v => indicator (hitsChain3 dec (d2Bad pr rb) emptyTable v.1))]
    apply lemmaA3 dec (d2Bad pr rb) (maxErr rb.ε pr.r) exp emptyTable Qtot (maxErr_nonneg _ _)
      (fun a T own pend g h => hCD a T own pend g h)
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
            indicator (hitsChain3 dec (d2Bad pr rb) emptyTable (eval H exp).1)) := mean_mono hpoint
    _ = mean (fun H : I → A => indicator (inj.Coll (eval H exp))) +
          mean (fun H : I → A =>
            indicator (hitsChain3 dec (d2Bad pr rb) emptyTable (eval H exp).1)) := mean_add _ _
    _ ≤ κ Qtot + (Qtot : ℚ) * maxErr rb.ε pr.r := add_le_add inj.mass hA
    _ = (Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot := add_comm _ _

#print axioms lemmaA3
#print axioms lemmaB3
#print axioms theorem43
end Main
end R0C.V3
