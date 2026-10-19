import R0FS.Hypotheses
import FS2.DuplexDecodes

/-! # R0 on the duplex (v2)

The v2 challenge of the duplex is `(value, next state)`; R0's state function
sees only the value.  `proj` drops the states; `doomed₂ := doomed ∘ proj`.
(D1), (D2′) and (D3) transfer from the v1 proofs: by `samp_mean` the round's
law on fresh answers is the law of the squeezed state through `σ_i`, which is
exactly v1's sampler with `k_i = 32` bytes. -/
set_option autoImplicit false
namespace R0FS.V2

open FS FS2 FS2.Duplex R0FS AspisR0.Opening AspisR0.ListsResponses
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisWide.InitialEncoder
noncomputable section
attribute [local irreducible] Close Lambda LambdaR

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E] {Sfield : Fin 29 → Subfield E}
variable {Pf : Type} {L : Nat}

/-- Drop the duplex states from a v2 prefix. -/
def proj (P : Prefix (Stmt E Sfield) (Msg E) (Duplex.Chal (R0FS.Chal E))) :
    Prefix (Stmt E Sfield) (Msg E) (R0FS.Chal E) :=
  ⟨P.statement, P.rounds.map fun r => (r.1, r.2.1)⟩

theorem proj_ext (P : Prefix (Stmt E Sfield) (Msg E) (Duplex.Chal (R0FS.Chal E))) (m : Msg E)
    (c : Duplex.Chal (R0FS.Chal E)) : proj (P.ext m c) = (proj P).ext m c.1 := by
  simp [proj, Prefix.ext]

theorem proj_round (P : Prefix (Stmt E Sfield) (Msg E) (Duplex.Chal (R0FS.Chal E))) :
    (proj P).round = P.round := by
  simp [proj, Prefix.round]

/-- The v1 parameter object induced by a duplex `σ` (32-byte samplers). -/
def params1 (p : Duplex.Params (Msg E) (R0FS.Chal E) L) (msg : Pf → Nat → Msg E) :
    R0FS.Params E Sfield Pf (Addr L) Byte 32 where
  k := fun _ => 32
  hk := fun _ => le_rfl
  sampler := fun i a => p.σ i a
  msg := msg
  addr := fun _ _ => default
  decode := fun _ _ => none

/-- The duplex sampler laws for R0: v1's laws on the 32-byte squeezed state. -/
def SamplerLawsD (p : Duplex.Params (Msg E) (R0FS.Chal E) L) (msg : Pf → Nat → Msg E) : Prop :=
  R0FS.SamplerLaws (params1 (Sfield := Sfield) p msg)

def rb2 : RoundByRound' (Stmt E Sfield) (Msg E) (Duplex.Chal (R0FS.Chal E)) (Addr L) State where
  doomed := fun P T => R0FS.doomed (proj P) T
  ε := R0FS.ε E

/-- The extractor, as a named function (route A: it ignores the table). -/
def extr := fun (x : Stmt E Sfield) (T : Table (Addr L) State) => R0FS.extract x T

variable (p : Duplex.Params (Msg E) (R0FS.Chal E) L) (x : Stmt E Sfield) (msg : Pf → Nat → Msg E)

local notation "pr" => Duplex.protocol p x msg (extr (Sfield := Sfield) (L := L))

theorem d1₂ : FS2.D1 (pr) rb2 := by
  intro x' T hx
  simp only [Duplex.protocol, extr] at hx
  have h := R0FS.d1 (params1 (Sfield := Sfield) p msg) x' T (by
    simp only [R0FS.protocol]
    exact hx)
  simp only [R0FS.roundByRound] at h
  simp only [rb2]
  exact h

theorem d2₂ (hr5 : p.rounds = 5) (hs : SamplerLawsD (Sfield := Sfield) p msg) :
    FS2.D2 (pr) rb2 := by
  intro i P m T' T hround hi hd
  have hround' : (proj P).round = i := by rw [proj_round]; exact hround
  have hi5 : i < 5 := by
    have : (pr).r = p.rounds := rfl
    rw [this, hr5] at hi; exact hi
  have hi' : i < (R0FS.protocol (params1 (Sfield := Sfield) p msg)).r := hi5
  have h2 := R0FS.d2 (params1 (Sfield := Sfield) p msg) hs i (proj P) m T' T hround' hi' hd
  change mean (fun a : Fin 32 → Byte => indicator (¬ R0FS.doomed ((proj P).ext m (p.σ i a)) T)) ≤
    R0FS.ε E i at h2
  change independentMean (samp p i P m).toProgram
    (fun w => indicator (¬ R0FS.doomed (proj (P.ext m w.2)) T)) ≤ R0FS.ε E i
  rw [independentMean_outcome _ (fun c : Duplex.Chal (R0FS.Chal E) =>
    indicator (¬ R0FS.doomed ((proj P).ext m c.1) T)) _ (fun w => by rw [proj_ext])]
  rw [samp_mean p i P m (fun c => ¬ R0FS.doomed ((proj P).ext m c.1) T)]
  rw [mean_congr (fun a => mean_const (indicator (¬ R0FS.doomed ((proj P).ext m (p.σ i a)) T)))]
  exact h2

def decision₂ (P : Prefix (Stmt E Sfield) (Msg E) (Duplex.Chal (R0FS.Chal E))) (m : Msg E) : Bool :=
  R0FS.decision (proj P) m

/-- The transcript depends on the protocol only through `msg` and `samp`. -/
theorem transcript_congr {X M C W Pf I A : Type} [DecidableEq I] [Inhabited A]
    (pr1 pr2 : FS2.Protocol X M C W Pf I A) (hm : pr1.msg = pr2.msg) (hs : pr1.samp = pr2.samp)
    (H : I → A) (x : X) (π : Pf) : ∀ n, pr1.transcript H x π n = pr2.transcript H x π n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [FS2.Protocol.transcript, ih, hm, hs]

local notation "prAt" x' => Duplex.protocol p x' msg (extr (Sfield := Sfield) (L := L))

theorem d3_at (hs : SamplerLawsD (Sfield := Sfield) p msg) (x' : Stmt E Sfield)
    (H : Addr L → State) (π : Pf) (T : Table (Addr L) State)
    (hd : rb2.doomed ((prAt x').transcript H x' π 5) T) :
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

theorem d3₂ (hr5 : p.rounds = 5) (hs : SamplerLawsD (Sfield := Sfield) p msg) :
    FS2.D3 (pr) rb2 (FS2.verifier (pr) decision₂) := by
  intro H x' π T hd
  rw [FS2.verifier_eval]
  have hr : (pr).r = 5 := hr5
  rw [hr] at hd ⊢
  have hT : (pr).transcript H x' π 5 = (prAt x').transcript H x' π 5 :=
    transcript_congr _ _ rfl rfl H x' π 5
  rw [hT] at hd ⊢
  exact d3_at p msg hs x' H π T hd

/-- R0 compiled with the duplex: the Fiat–Shamir bound `Q_tot · 2^-105.14 +
2·Q_tot²/2^256` from the sampler laws and the query bound alone. -/
theorem r0_duplex_fiat_shamir (hr5 : p.rounds = 5) (hs : SamplerLawsD (Sfield := Sfield) p msg)
    (x : Stmt E Sfield) (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P
      (FS2.verifier (prAt x) decision₂) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
        indicator (FS2.accepts (eval H (FS2.experiment P (FS2.verifier (prAt x) decision₂) x)) ∧
          FS2.extractFails (prAt x) x (eval H (FS2.experiment P (FS2.verifier (prAt x) decision₂) x)))) ≤
      (Qtot : ℚ) * maxErr (R0FS.ε E) p.rounds + κ Qtot :=
  duplex_fiat_shamir_verifier p x msg (extr (Sfield := Sfield) (L := L)) decision₂ P Qtot rb2
    (d1₂ p x msg) (d2₂ p x msg hr5 hs) (d3₂ p x msg hr5 hs) hQ

#print axioms r0_duplex_fiat_shamir
#print axioms d1₂
#print axioms d2₂
#print axioms d3₂
end
end R0FS.V2
