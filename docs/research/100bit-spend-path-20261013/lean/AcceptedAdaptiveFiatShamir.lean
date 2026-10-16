import AllAddressFiatShamirOutside

/-! The existing adaptive first-read reduction only needs decoder completion
on accepting executions. Invalid-format rejecting runs need not be assigned a
fake public/proof or charged as collisions. This is the same first-bad-event
proof with the recovery premise explicitly restricted to accepting runs.
The query-dependent bound and terminal D3 obligations are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.AcceptedAdaptiveFiatShamir

open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleFiniteSupport

variable {X M C W Pf I A Y : Type} [DecidableEq I] [Inhabited A] [Fintype A]

def experiment (P : Program I A (X × Pf))
    (V : X → Pf → Program I A Bool) : Program I A ((X × Pf) × Bool) :=
  FS2.experiment P (fun (_ : Unit) xp => V xp.1 xp.2) ()

def extractFails (pr : FS2.Protocol X M C W Pf I A)
    (v : View I A ((X × Pf) × Bool)) : Prop :=
  FS2.extractFails pr v.2.1.1 (v.1, (v.2.1.2, v.2.2))

structure LazyInj (pr : FS2.Protocol X M C W Pf I A)
    (dec : Dec X M C I A Y) (P : Program I A (X × Pf))
    (V : X → Pf → Program I A Bool) (κ : Nat → ℚ) (Qtot : Nat) where
  Coll : View I A ((X × Pf) × Bool) → Prop
  mass : lazyMean (experiment P V) emptyTable (fun v => indicator (Coll v)) ≤ κ Qtot
  decodes : ∀ H : I → A, ¬ Coll (eval H (experiment P V)) →
    accepts (eval H (experiment P V)) →
    ∀ i a, i < pr.r →
      firstCell (pr.chain H (eval H (experiment P V)).2.1.1
        (eval H (experiment P V)).2.1.2 i) = some a →
      ∃ own pend g, dec a (tableBefore emptyTable (eval H (experiment P V)).1 a) =
          some (own, pend, g) ∧
        bfollow g (traceFrom (eval H (experiment P V)).1 a) own pend
          (tableBefore emptyTable (eval H (experiment P V)).1 a) =
          some (pr.transcript H (eval H (experiment P V)).2.1.1
              (eval H (experiment P V)).2.1.2 i,
            pr.msg (eval H (experiment P V)).2.1.2 i,
            pr.chal H (eval H (experiment P V)).2.1.1
              (eval H (experiment P V)).2.1.2 i)

def D3Outside (pr : FS2.Protocol X M C W Pf I A)
    (rb : RoundByRound' X M C I A) (P : Program I A (X × Pf))
    (V : X → Pf → Program I A Bool)
    (Coll : View I A ((X × Pf) × Bool) → Prop) : Prop :=
  ∀ (H : I → A) (T : Table I A),
    ¬ Coll (eval H (experiment P V)) →
    rb.doomed (pr.transcript H (eval H P).2.1 (eval H P).2.2 pr.r) T →
    (eval H (V (eval H P).2.1 (eval H P).2.2)).2 = false

theorem first_bad_outside (pr : FS2.Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (dec : Dec X M C I A Y) (P : Program I A (X × Pf)) (V : X → Pf → Program I A Bool)
    (κ : Nat → ℚ) (Qtot : Nat) (hD1 : FS2.D1 pr rb)
    (hreads : ChainsRead pr) (hV : ReadsChains pr V) (inj : LazyInj pr dec P V κ Qtot)
    (hD3 : D3Outside pr rb P V inj.Coll)
    (H : I → A) (hcoll : ¬ inj.Coll (eval H (experiment P V)))
    (hacc : accepts (eval H (experiment P V)))
    (hfail : extractFails pr (eval H (experiment P V))) :
    hitsChain3 dec (d2Bad pr rb) emptyTable (eval H (experiment P V)).1 := by
  set v := eval H (experiment P V) with hv
  set x := (eval H P).2.1 with hxdef
  set π := (eval H P).2.2 with hπdef
  have hx : v.2.1.1 = x := by rw [hv, experiment, FS2.experiment_eval]
  have hπ : v.2.1.2 = π := by rw [hv, experiment, FS2.experiment_eval]
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
    simp only [extractFails, FS2.extractFails, hx, hπ] at hfail
    simp only [T, FS2.Protocol.chain, FS2.Protocol.transcript]
    cases h : firstCell (pr.samp 0 (emptyPrefix x) (pr.msg π 0)) <;>
      simp only [h] at hfail ⊢ <;> exact hfail
  have er : ¬ e pr.r := by
    intro hr
    have hrej := hD3 H _ hcoll hr
    have : v.2.2 = (eval H (V x π)).2 := by rw [hv, experiment, FS2.experiment_eval]
    simp only [FS2.accepts] at hacc
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
    rw [hv, experiment, FS2.experiment_eval, List.map_append, List.mem_append]
    exact Or.inr this
  have hdec := inj.decodes H hcoll hacc i a hi
  rw [← hv, hx, hπ] at hdec
  obtain ⟨own, pend, g, hS, hf⟩ := hdec ha
  apply hitsChain3_of_first dec (d2Bad pr rb) a v.1 emptyTable hmem rfl
  refine ⟨own, pend, g, pr.transcript H x π i, pr.msg π i, pr.chal H x π i, hS, hf, ?_⟩
  refine ⟨by rw [FS2.transcript_round]; exact hi, hdoomed, ?_⟩
  rw [← hT]
  exact hnot'

theorem soundness_bound_outside (pr : FS2.Protocol X M C W Pf I A)
    (rb : RoundByRound' X M C I A) (dec : Dec X M C I A Y)
    (P : Program I A (X × Pf)) (V : X → Pf → Program I A Bool)
    (κ : Nat → ℚ) (Qtot : Nat)
    (hD1 : FS2.D1 pr rb) (hCD : ChainDensity3 pr rb dec)
    (hreads : ChainsRead pr) (hV : ReadsChains pr V)
    (inj : LazyInj pr dec P V κ Qtot)
    (hD3 : D3Outside pr rb P V inj.Coll)
    (hQ : ∀ H : I → A, distinctFirstReads (eval H (experiment P V)) ≤ Qtot) :
    lazyMean (experiment P V) emptyTable
      (fun v => indicator (accepts v ∧ extractFails pr v)) ≤
      (Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot := by
  let exp := experiment P V
  have hpoint : ∀ H : I → A,
      indicator (accepts (eval H exp) ∧ extractFails pr (eval H exp)) ≤
        indicator (inj.Coll (eval H exp)) +
          indicator (hitsChain3 dec (d2Bad pr rb) emptyTable (eval H exp).1) := by
    intro H
    refine le_trans (indicator_mono ?_) (indicator_or_le _ _)
    rintro ⟨hacc, hfail⟩
    by_cases hc : inj.Coll (eval H exp)
    · exact Or.inl hc
    · exact Or.inr (first_bad_outside pr rb dec P V κ Qtot hD1 hreads hV inj hD3 H hc hacc hfail)
  have hA : lazyMean exp emptyTable
      (fun v => indicator (hitsChain3 dec (d2Bad pr rb) emptyTable v.1)) ≤
        (Qtot : ℚ) * maxErr rb.ε pr.r := by
    apply lemmaA3 dec (d2Bad pr rb) (maxErr rb.ε pr.r) exp emptyTable Qtot
      (maxErr_nonneg _ _) (fun a T own pend g h => hCD a T own pend g h)
    apply firstReadsBound_of_traces
    intro H
    exact hQ H
  calc
    lazyMean exp emptyTable (fun v => indicator (accepts v ∧ extractFails pr v)) ≤
        lazyMean exp emptyTable (fun v => indicator (inj.Coll v) +
          indicator (hitsChain3 dec (d2Bad pr rb) emptyTable v.1)) :=
      AllAddressFiatShamir.lazyMean_mono_of_eval exp _ _ hpoint
    _ = lazyMean exp emptyTable (fun v => indicator (inj.Coll v)) +
        lazyMean exp emptyTable (fun v => indicator (hitsChain3 dec (d2Bad pr rb) emptyTable v.1)) :=
      lazyMean_add _ _ _ _
    _ ≤ κ Qtot + (Qtot : ℚ) * maxErr rb.ε pr.r := add_le_add inj.mass hA
    _ = _ := add_comm _ _

#print axioms first_bad_outside
#print axioms soundness_bound_outside
end AspisR1.AcceptedAdaptiveFiatShamir
end
