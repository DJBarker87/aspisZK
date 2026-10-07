import R0C.SlackDensity

/-! Scaled D2-prime and conditional assembly for the UNCHANGED one-block
concrete duplex. This does not assert a concrete q22 instance of the law. -/
set_option autoImplicit false
namespace R0C.SlackDuplex
open FS FS2 FS2.Duplex R0FS R0FS.V2 R0C.SlackStatement AspisR0.Opening AspisR0.ListsResponses
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisWide.InitialEncoder
noncomputable section
attribute [local irreducible] Close Lambda LambdaR

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E] {Sfield : Fin 29 → Subfield E}
variable {Pf : Type} {L : Nat}

variable {δ : ℚ}

variable (p : Duplex.Params (Msg E) (R0FS.Chal E) L) (x : Stmt E Sfield) (msg : Pf → Nat → Msg E)

local notation "pr" => Duplex.protocol p x msg (extr (Sfield := Sfield) (L := L))

theorem d1_slack (δ : ℚ) : FS2.D1 (pr) (rb2Slack δ) :=
  R0FS.V2.d1₂ p x msg

theorem d2_slack (hr5 : p.rounds = 5) (hδ : 0 ≤ δ) (hs : SamplerLawsSlackD (Sfield := Sfield) δ p msg) :
    FS2.D2 (pr) (rb2Slack δ) := by
  intro i P m T' T hround hi hd
  have hround' : (proj P).round = i := by rw [proj_round]; exact hround
  have hi5 : i < 5 := by
    have : (pr).r = p.rounds := rfl
    rw [this, hr5] at hi; exact hi
  have hi' : i < (R0FS.protocol (params1 (Sfield := Sfield) p msg)).r := hi5
  have h2 := SlackDensity.d2 (params1 (Sfield := Sfield) p msg) hδ hs i (proj P) m T' T hround' hi' hd
  change mean (fun a : Fin 32 → Byte => indicator (¬ R0FS.doomed ((proj P).ext m (p.σ i a)) T)) ≤
    epsilonSlack E δ i at h2
  change independentMean (samp p i P m).toProgram
    (fun w => indicator (¬ R0FS.doomed (proj (P.ext m w.2)) T)) ≤ epsilonSlack E δ i
  rw [independentMean_outcome _ (fun c : Duplex.Chal (R0FS.Chal E) =>
    indicator (¬ R0FS.doomed ((proj P).ext m c.1) T)) _ (fun w => by rw [proj_ext])]
  rw [samp_mean p i P m (fun c => ¬ R0FS.doomed ((proj P).ext m c.1) T)]
  rw [mean_congr (fun a => mean_const (indicator (¬ R0FS.doomed ((proj P).ext m (p.σ i a)) T)))]
  exact h2
local notation "prAt" x' => Duplex.protocol p x' msg (extr (Sfield := Sfield) (L := L))

theorem d3_at_slack (hs : SamplerLawsSlackD (Sfield := Sfield) δ p msg) (x' : Stmt E Sfield)
    (H : Addr L → State) (π : Pf) (T : Table (Addr L) State)
    (hd : (rb2Slack δ).doomed ((prAt x').transcript H x' π 5) T) :
    decision₂ ((prAt x').transcript H x' π 5) (msg π 5) = false := by
  by_contra hacc
  have hacc' : decision₂ ((prAt x').transcript H x' π 5) (msg π 5) = true := by
    rcases h : decision₂ ((prAt x').transcript H x' π 5) (msg π 5)
    · exact absurd h hacc
    · rfl
  obtain ⟨y, γ, v, κ, τ, Q, α, F, S, hrs, _, hAcc⟩ := decision_true _ _ hacc'
  have hrs0 := hrs
  have hstmt : (proj ((prAt x').transcript H x' π 5)).statement = x' :=
    FS2.Duplex.transcript_statement p x' msg (extr (Sfield := Sfield) (L := L)) H π 5
  rw [hstmt] at hAcc
  have hrounds : (proj ((prAt x').transcript H x' π 5)).rounds =
      (List.range 5).map fun j => (msg π j, p.σ j (H (sqC p x' msg (extr (Sfield := Sfield) (L := L)) H π j))) := by
    simp only [proj, FS2.Duplex.transcript_rounds, List.map_map, FS2.Duplex.chal_eq]
    rfl
  have e := hrs0.symm.trans hrounds
  have hR : ((List.range 5).map fun j => (msg π j, p.σ j (H (sqC p x' msg (extr (Sfield := Sfield) (L := L)) H π j)))) =
      [(msg π 0, p.σ 0 (H (sqC p x' msg (extr (Sfield := Sfield) (L := L)) H π 0))),
       (msg π 1, p.σ 1 (H (sqC p x' msg (extr (Sfield := Sfield) (L := L)) H π 1))),
       (msg π 2, p.σ 2 (H (sqC p x' msg (extr (Sfield := Sfield) (L := L)) H π 2))),
       (msg π 3, p.σ 3 (H (sqC p x' msg (extr (Sfield := Sfield) (L := L)) H π 3))),
       (msg π 4, p.σ 4 (H (sqC p x' msg (extr (Sfield := Sfield) (L := L)) H π 4)))] := rfl
  rw [hR] at e
  injection e with e0 e
  injection e with e1 e
  injection e with e2 e
  injection e with e3 e
  injection e with e4 _
  injection e0 with _ hc0
  injection e4 with _ hc4
  have hγ : γ ≠ 0 := by
    obtain ⟨c, hc, hne⟩ := hs.nonzero (H (sqC p x' msg (extr (Sfield := Sfield) (L := L)) H π 0))
    change p.σ 0 _ = _ at hc
    rw [hc] at hc0
    cases hc0
    exact hne
  have hScard : S.card = 22 := by
    obtain ⟨S', hS', hcard⟩ := hs.queryCard (H (sqC p x' msg (extr (Sfield := Sfield) (L := L)) H π 4))
    change p.σ 4 _ = _ at hS'
    rw [hS'] at hc4
    cases hc4
    exact hcard
  apply accept_not_doomed x' y γ v κ τ α Q F S T hγ hScard hAcc
  have hP : proj ((prAt x').transcript H x' π 5) = ⟨x', [(.values y, .field γ), (.scalar v, .field κ),
      (.unit, .field τ), (.poly Q, .field α), (.final F, .set S)]⟩ := by
    cases h : proj ((prAt x').transcript H x' π 5) with
    | mk st rs =>
        rw [h] at hstmt hrs0
        simp only at hstmt hrs0
        rw [hstmt, hrs0]
  rw [← hP]
  exact hd

theorem d3_slack (hr5 : p.rounds = 5) (hs : SamplerLawsSlackD (Sfield := Sfield) δ p msg) :
    FS2.D3 (pr) (rb2Slack δ) (FS2.verifier (pr) decision₂) := by
  intro H x' π T hd
  rw [FS2.verifier_eval]
  have hr : (pr).r = 5 := hr5
  rw [hr] at hd ⊢
  have hT : (pr).transcript H x' π 5 = (prAt x').transcript H x' π 5 :=
    transcript_congr _ _ rfl rfl H x' π 5
  rw [hT] at hd ⊢
  exact d3_at_slack p msg hs x' H π T hd

/-- Conditional transport only: the retained q22 program has a different
read shape and cannot supply this total one-block law at delta0. -/
theorem r0_duplex_fiat_shamir_slack_of_laws (hr5 : p.rounds = 5) (hδ : 0 ≤ δ) (hs : SamplerLawsSlackD (Sfield := Sfield) δ p msg)
    (x : Stmt E Sfield) (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P
      (FS2.verifier (prAt x) decision₂) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
        indicator (FS2.accepts (eval H (FS2.experiment P (FS2.verifier (prAt x) decision₂) x)) ∧
          FS2.extractFails (prAt x) x (eval H (FS2.experiment P (FS2.verifier (prAt x) decision₂) x)))) ≤
      (Qtot : ℚ) * maxErr (epsilonSlack E δ) p.rounds + κ Qtot :=
  duplex_fiat_shamir_verifier p x msg (extr (Sfield := Sfield) (L := L)) decision₂ P Qtot (rb2Slack δ)
    (d1_slack p x msg δ) (d2_slack p x msg hr5 hδ hs) (d3_slack p x msg hr5 hs) hQ


#print axioms d1_slack
#print axioms d2_slack
#print axioms d3_slack
#print axioms r0_duplex_fiat_shamir_slack_of_laws
end
end R0C.SlackDuplex
