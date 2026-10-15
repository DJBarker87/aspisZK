import R0C.V3.Gen
import AspisV8R19.OracleFiniteSupport

/-! The v3 conditional first-read bound with arbitrary address types.
The experiment law is memoized lazy sampling: no finite-address assumption,
input-length bound, address encoder or overlength fallback is present.
Decoder injection and its collision mass remain explicit obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.AllAddressFiatShamir

open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleFiniteSupport

variable {X M C W Pf I A Y : Type} [DecidableEq I] [Inhabited A] [Fintype A]

structure LazyInj (pr : FS2.Protocol X M C W Pf I A) (dec : Dec X M C I A Y) (P : Program I A Pf)
    (V : X → Pf → Program I A Bool) (x : X) (κ : Nat → ℚ) (Qtot : Nat) where
  Coll : View I A (Pf × Bool) → Prop
  mass : lazyMean (experiment P V x) emptyTable (fun v => indicator (Coll v)) ≤ κ Qtot
  decodes : ∀ H : I → A, ¬ Coll (eval H (experiment P V x)) →
    ∀ i a, i < pr.r →
      firstCell (pr.chain H x (eval H (experiment P V x)).2.1 i) = some a →
      ∃ own pend g, dec a (tableBefore emptyTable (eval H (experiment P V x)).1 a) =
          some (own, pend, g) ∧
        bfollow g (traceFrom (eval H (experiment P V x)).1 a) own pend
          (tableBefore emptyTable (eval H (experiment P V x)).1 a) =
          some (pr.transcript H x (eval H (experiment P V x)).2.1 i,
            pr.msg (eval H (experiment P V x)).2.1 i, pr.chal H x (eval H (experiment P V x)).2.1 i)

theorem first_bad (pr : FS2.Protocol X M C W Pf I A) (rb : RoundByRound' X M C I A)
    (dec : Dec X M C I A Y) (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat) (hD1 : FS2.D1 pr rb) (hD3 : FS2.D3 pr rb V)
    (hreads : ChainsRead pr) (hV : ReadsChains pr V) (inj : LazyInj pr dec P V x κ Qtot)
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
    simp only [FS2.extractFails, hπ] at hfail
    simp only [T, FS2.Protocol.chain, FS2.Protocol.transcript]
    cases h : firstCell (pr.samp 0 (emptyPrefix x) (pr.msg π 0)) <;>
      simp only [h] at hfail ⊢ <;> exact hfail
  have er : ¬ e pr.r := by
    intro hr
    have hrej := hD3 H x π _ hr
    have : v.2.2 = (eval H (V x π)).2 := by rw [hv, FS2.experiment_eval]
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

theorem lazyMean_mono_of_eval {O : Type} (p : Program I A O)
    (f g : View I A O → ℚ)
    (h : ∀ H : I → A, f (eval H p) ≤ g (eval H p)) :
    lazyMean p emptyTable f ≤ lazyMean p emptyTable g := by
  calc
    lazyMean p emptyTable f =
        mean (fun H => f (eval (extend (support p) H default) p)) :=
      (finite_support_oracle_law p (support p) (fun _ hi => hi) default f).symm
    _ ≤ mean (fun H => g (eval (extend (support p) H default) p)) :=
      mean_mono (fun H => h (extend (support p) H default))
    _ = lazyMean p emptyTable g :=
      finite_support_oracle_law p (support p) (fun _ hi => hi) default g

theorem soundness_bound (pr : FS2.Protocol X M C W Pf I A)
    (rb : RoundByRound' X M C I A) (dec : Dec X M C I A Y)
    (P : Program I A Pf) (V : X → Pf → Program I A Bool) (x : X)
    (κ : Nat → ℚ) (Qtot : Nat)
    (hD1 : FS2.D1 pr rb) (hCD : ChainDensity3 pr rb dec)
    (hD3 : FS2.D3 pr rb V) (hreads : ChainsRead pr) (hV : ReadsChains pr V)
    (inj : LazyInj pr dec P V x κ Qtot)
    (hQ : ∀ H : I → A, distinctFirstReads (eval H (experiment P V x)) ≤ Qtot) :
    lazyMean (experiment P V x) emptyTable
      (fun v => indicator (accepts v ∧ extractFails pr x v)) ≤
      (Qtot : ℚ) * maxErr rb.ε pr.r + κ Qtot := by
  let exp := experiment P V x
  have hpoint : ∀ H : I → A,
      indicator (accepts (eval H exp) ∧ extractFails pr x (eval H exp)) ≤
        indicator (inj.Coll (eval H exp)) +
          indicator (hitsChain3 dec (d2Bad pr rb) emptyTable (eval H exp).1) := by
    intro H
    refine le_trans (indicator_mono ?_) (indicator_or_le _ _)
    rintro ⟨hacc, hfail⟩
    by_cases hc : inj.Coll (eval H exp)
    · exact Or.inl hc
    · exact Or.inr (first_bad pr rb dec P V x κ Qtot hD1 hD3 hreads hV inj H hc hacc hfail)
  have hA : lazyMean exp emptyTable
      (fun v => indicator (hitsChain3 dec (d2Bad pr rb) emptyTable v.1)) ≤
        (Qtot : ℚ) * maxErr rb.ε pr.r := by
    apply lemmaA3 dec (d2Bad pr rb) (maxErr rb.ε pr.r) exp emptyTable Qtot
      (maxErr_nonneg _ _) (fun a T own pend g h => hCD a T own pend g h)
    apply firstReadsBound_of_traces
    intro H
    exact hQ H
  calc
    lazyMean exp emptyTable (fun v => indicator (accepts v ∧ extractFails pr x v)) ≤
        lazyMean exp emptyTable (fun v => indicator (inj.Coll v) +
          indicator (hitsChain3 dec (d2Bad pr rb) emptyTable v.1)) :=
      lazyMean_mono_of_eval exp _ _ hpoint
    _ = lazyMean exp emptyTable (fun v => indicator (inj.Coll v)) +
        lazyMean exp emptyTable (fun v => indicator (hitsChain3 dec (d2Bad pr rb) emptyTable v.1)) :=
      lazyMean_add _ _ _ _
    _ ≤ κ Qtot + (Qtot : ℚ) * maxErr rb.ε pr.r := add_le_add inj.mass hA
    _ = _ := add_comm _ _

#print axioms first_bad
#print axioms lazyMean_mono_of_eval
#print axioms soundness_bound
end AspisR1.AllAddressFiatShamir
end
