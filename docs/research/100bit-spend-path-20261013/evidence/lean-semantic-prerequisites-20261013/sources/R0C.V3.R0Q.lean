import R0C.V3.DQDecodes
import R0C.SlackBits

/-! # R0 compiled with the duplex, q22 round included

`r0_q22_fiat_shamir`: for R0's opening layer compiled with the duplex of
`AspisV8R19.DuplexFrames`, the concrete 32-byte field sampler for γ, κ, τ, α₀,
the tree's q22 query sampler (all eight chain blocks read, failure rejected)
and the chain-running verifier,

  Pr[V accepts ∧ no witness] ≤ Q_tot · max_i εδ₀_i + 2·Q_tot²/2^256,

with no sampler premise.  Premise SEM and the step-3 challenge conditions
remain inside the statement `x`. -/
set_option autoImplicit false
namespace R0C.V3.DQ

open FS FS2 FS2.Duplex R0FS R0FS.V2 R0C.V3
open AspisR0.Opening AspisR0.ListsResponses
open AspisV8R19.MemoizedProgramLaw AspisV8PairedCommitment
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
noncomputable section
attribute [local irreducible] Close Lambda LambdaR

variable {Sfield : Fin 29 → Subfield E} {Pf : Type} {L : Nat}
variable (p : Duplex.Params (Msg E) (R0FS.Chal E) L) (x : Stmt E Sfield) (msg : Pf → Nat → Msg E)

local notation "prQ" => protocolQ (Sfield := Sfield) p x msg

/-- The q22 round's set has 22 fibres (a failed run gives `∅`). -/
def cardOK (P : Prefix (Stmt E Sfield) (Msg E) (R0FS.Chal E)) : Bool :=
  match P.rounds.getLast? with
  | some (_, .set S) => S.card == 22
  | _ => false

def decisionQ (P : Prefix (Stmt E Sfield) (Msg E) DC) (m : Msg E) : Bool :=
  R0FS.decision (proj P) m && cardOK (proj P)

local notation "VQ" => FS2.verifier (protocolQ (Sfield := Sfield) p x msg) decisionQ

theorem transcript_rounds_gen {X M C W Pf' I A : Type} [DecidableEq I] [Inhabited A]
    (pr : FS2.Protocol X M C W Pf' I A) (H : I → A) (x' : X) (π : Pf') :
    ∀ n, (pr.transcript H x' π n).rounds = (List.range n).map fun j => (pr.msg π j, pr.chal H x' π j) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show ((pr.transcript H x' π n).ext (pr.msg π n) _).rounds = _
      rw [Prefix.ext, ih, List.range_succ, List.map_append, List.map_singleton]
      rfl

theorem transcript_statement_gen {X M C W Pf' I A : Type} [DecidableEq I] [Inhabited A]
    (pr : FS2.Protocol X M C W Pf' I A) (H : I → A) (x' : X) (π : Pf') :
    ∀ n, (pr.transcript H x' π n).statement = x' := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem firstCell_mem {C : Type} (H : Addr L → State) (s : FS2.Sampler (Addr L) State C) (a : Addr L)
    (h : firstCell s = some a) : a ∈ (eval H s.toProgram).1.map Prod.fst := by
  cases s with
  | done c => simp [firstCell] at h
  | ask i k =>
      simp only [firstCell, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
  | multi c cs nd k =>
      simp only [firstCell, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..

theorem d1Q : FS2.D1 (prQ) (rbQ (Sfield := Sfield) (L := L)) := by
  intro x' T hx
  exact d1₂ p x msg x' T hx

theorem bool_true_of_ne_false {b : Bool} (h : ¬ b = false) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

theorem d3Q (hr5 : p.rounds = 5) (hσ : ∀ i s, i < 4 → p.σ i s = σQ i s) :
    FS2.D3 (prQ) (rbQ (Sfield := Sfield) (L := L)) (VQ) := by
  intro H x' π T hd
  rw [FS2.verifier_eval]
  have hr : (prQ).r = 5 := hr5
  rw [hr] at hd ⊢
  by_contra hacc
  have hacc' := bool_true_of_ne_false hacc
  simp only [decisionQ, Bool.and_eq_true] at hacc'
  obtain ⟨hdec, hcard⟩ := hacc'
  obtain ⟨y, γ, v, κ, τ, Q, α, F, S, hrs, _, hAcc⟩ := decision_true _ _ hdec
  have hstmt : (proj ((prQ).transcript H x' π 5)).statement = x' :=
    transcript_statement_gen (prQ) H x' π 5
  rw [hstmt] at hAcc
  have hS : S.card = 22 := by
    simp only [cardOK, hrs] at hcard
    simpa using hcard
  have hγ : γ ≠ 0 := by
    have hr0 : (proj ((prQ).transcript H x' π 5)).rounds.head? = some (msg π 0, ((prQ).chal H x' π 0).1) := by
      show ((prQ).transcript H x' π 5).rounds.head?.map (fun r => (r.1, r.2.1)) = _
      rw [transcript_rounds_gen]
      rfl
    rw [hrs] at hr0
    simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hr0
    have hc := hr0.2
    have e : protocolQ (Sfield := Sfield) p x msg = protocolQ (Sfield := Sfield) p x' msg := rfl
    rw [e, chalQ_lt p x' msg H π 0 (by omega), chal_eq, hσ 0 _ (by omega)] at hc
    simp only [σQ] at hc
    cases hc
    exact R0C.ModuloField.gamma_ne_zero _
  apply accept_not_doomed x' y γ v κ τ α Q F S T hγ hS hAcc
  have hP : proj ((prQ).transcript H x' π 5) = ⟨x', [(.values y, .field γ), (.scalar v, .field κ),
      (.unit, .field τ), (.poly Q, .field α), (.final F, .set S)]⟩ := by
    cases h : proj ((prQ).transcript H x' π 5) with
    | mk st rs =>
        rw [h] at hstmt hrs
        simp only at hstmt hrs
        rw [hstmt, hrs]
  rw [← hP]
  exact hd

theorem chainsReadQ : ChainsRead (prQ) := by
  intro i P m _
  show firstCell (sampQ p i P m) ≠ none
  unfold sampQ
  split <;> simp [firstCell, Duplex.samp]

theorem readsChainsQ : ReadsChains (prQ) (VQ) := by
  intro H x' π j a hj ha
  exact FS2.verifier_reads (prQ) decisionQ H x' π j hj a (firstCell_mem H _ a ha)

/-- R0 compiled with the duplex, q22 round included: no sampler premise. -/
theorem r0_q22_fiat_shamir (hr5 : p.rounds = 5) (hσ : ∀ i s, i < 4 → p.σ i s = σQ i s)
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P (VQ) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
        indicator (FS2.accepts (eval H (FS2.experiment P (VQ) x)) ∧
          FS2.extractFails (prQ) x (eval H (FS2.experiment P (VQ) x)))) ≤
      (Qtot : ℚ) * maxErr (R0C.SlackStatement.epsilonSlack E R0C.SlackStatement.delta0) 5 + κ Qtot := by
  have h := theorem43 (prQ) (rbQ (Sfield := Sfield) (L := L)) (decQ p x) P (VQ) x κ Qtot
    (d1Q p x msg) (chainDensityQ p x msg hr5 hσ) (d3Q p x msg hr5 hσ) (chainsReadQ p x msg)
    (readsChainsQ p x msg)
    { Coll := Coll p Qtot
      mass := coll_mass p Qtot P (VQ) x hQ
      decodes := fun H hc i a hi ha => decodesQ p x msg hr5 decisionQ P Qtot hQ H hc i a hi ha }
    hQ
  have hr : (prQ).r = 5 := hr5
  rw [hr] at h
  exact h

/-- The bound in closed form: `max_i εδ₀_i` is the q22 row, `(1+δ₀)·C(9557,22)/C(262144,22)`
(about 2^-105.136). -/
theorem r0_q22_fiat_shamir_closed (hr5 : p.rounds = 5) (hσ : ∀ i s, i < 4 → p.σ i s = σQ i s)
    (P : Program (Addr L) State Pf) (Qtot : Nat)
    (hQ : ∀ H, FS2.distinctFirstReads (eval H (FS2.experiment P (VQ) x)) ≤ Qtot) :
    mean (fun H : Addr L → State =>
        indicator (FS2.accepts (eval H (FS2.experiment P (VQ) x)) ∧
          FS2.extractFails (prQ) x (eval H (FS2.experiment P (VQ) x)))) ≤
      (Qtot : ℚ) * ((1 + R0C.SlackStatement.delta0) *
        ((Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ))) + κ Qtot := by
  have h := r0_q22_fiat_shamir p x msg hr5 hσ P Qtot hQ
  rw [R0C.SlackBits.max_error_query] at h
  exact h

#print axioms r0_q22_fiat_shamir
#print axioms r0_q22_fiat_shamir_closed
end
end R0C.V3.DQ
