import R1Z.ProverCommitQuotientLaw
import R1Z.ProverCommitQuotientView
import R1Z.PrivacyR1PBin

/-! The existing real coupling, with only its middle tape completed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitQuotientCoupling
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsAbortBounds R0Z.HvzkV
  R1Z.Batched R1Z.LensR1 R1Z.TranscriptR1 R1Z.GamesR1 R1Z.LazyFrozen R1Z.GamesR1PBin
  R1Z.CouplingR1PBin R1Z.ProverCommitTapeCompletion
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (eCm : W.Cm ≃ (RIdx → OracleAnswer))

def gMQ (a : AttS (F := F) W Pr) : R1Coins W.Cm W.Tab × Tape K F :=
  ((gM W Pr eCm a).1, completeOrSpare
    (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) => Pr.tapeOf e.1 e.2)
    ((e₁Of a.2.1, e₂Of a.2.1), a.2.2.1))

def toMQ {N : ℕ} (s : Fin N → AttS (F := F) W Pr) :
    (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F) :=
  (fun k => (gMQ W Pr eCm (s k)).1, fun k => (gMQ W Pr eCm (s k)).2)

theorem mp_gMQ (cF : ℕ)
    (hfib : ∀ τ : SourceTape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        quotientDecode (fun e => Pr.tapeOf e.1 e.2) e = some τ)).card = cF) :
    MP (gMQ W Pr eCm) := by
  have hd := mp_completeOrSpare (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
    Pr.tapeOf e.1 e.2) cF (fun q => by convert hfib q)
  have h1 : MP (fun a : AttS (F := F) W Pr => a.2) := mp_snd
  have h2 : MP (fun p : (Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) × (Tape K F × W.Tab) =>
      (eV W Pr p.1, (Equiv.refl (Tape K F × W.Tab)) p.2)) :=
    mp_prodMap (mp_equiv (eV W Pr)) (mp_equiv (Equiv.refl _))
  have h3 := mp_equiv (rearr (A₁ := TRead → OracleAnswer) (A₂ := Fin 3 → OracleAnswer)
    (E := (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) (A₄ := RIdx → OracleAnswer)
    (T := Tape K F) (B := W.Tab))
  have h4 := mp_prodMap (mp_equiv (eC W eCm)) hd
  have hc := mp_comp (mp_comp (mp_comp h1 h2) h3) h4
  intro f
  exact hc f

theorem meanM_Q (cF : ℕ)
    (hfib : ∀ τ : SourceTape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        quotientDecode (fun e => Pr.tapeOf e.1 e.2) e = some τ)).card = cF) (N : ℕ)
    (f : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F) → ℚ) :
    mean (fun s : Fin N → AttS (F := F) W Pr => f (toMQ W Pr eCm s)) = mean f := by
  have hp := mp_pi (mp_gMQ W Pr eCm cF hfib) N
  have he := mp_equiv (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => R1Coins W.Cm W.Tab)
    (fun _ => Tape K F))
  exact (mp_comp hp he) f

theorem completed_view (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (ch : Challenges K)
    (a : AttS (F := F) W Pr) :
    view (Bat := R1Bat) h B outputs x w ch (gMQ W Pr eCm a).2 =
      view h B outputs x w ch (gM W Pr eCm a).2 := by
  cases ht : Pr.tapeOf (e₁Of a.2.1) (e₂Of a.2.1) with
  | none => simp only [gMQ, gM, completeOrSpare, quotientDecode, ht,
      Option.map_none, Option.getD_none, complete_project]
  | some t =>
    simpa only [gMQ, gM, completeOrSpare, quotientDecode, ht,
      Option.map_some, Option.getD_some] using view_completion h B outputs x w ch t (padding a.2.2.1)

theorem retryTest_tapes {C T O : Type} (N : ℕ) (Pd : C → Prop) (pub : C → T → O)
    (ext : (Fin N → C) → Fin N → O → ℚ) (fail : (Fin N → C) → ℚ)
    (coins : Fin N → C) (t u : Fin N → T)
    (same : ∀ k, pub (coins k) (t k) = pub (coins k) (u k)) :
    retryTest N Pd pub ext fail (coins, t) = retryTest N Pd pub ext fail (coins, u) := by
  unfold retryTest
  cases hk : firstGood Pd coins with
  | none => rfl
  | some k => exact congrArg (ext coins k) (same k)

theorem middle_completion (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (V : Challenges K → h.Instance → Prop) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (adv : (fsR1P W Pr N hN P Vp).Adversary)
    (x : Statement K CommitHandle) (w : h.Instance) (s : Fin N → AttS (F := F) W Pr) :
    middleRealAbortV P h V B outputs (fsR1P W Pr N hN P Vp) (abR1P W N hN) adv x w (toMQ W Pr eCm s) =
    middleRealAbortV P h V B outputs (fsR1P W Pr N hN P Vp) (abR1P W N hN) adv x w (toMP W Pr eCm s) := by
  apply retryTest_tapes
  intro k
  exact completed_view W Pr eCm h B outputs x w _ (s k)

#print axioms mp_gMQ
#print axioms meanM_Q
#print axioms completed_view
#print axioms retryTest_tapes
#print axioms middle_completion
end R1Z.ProverCommitQuotientCoupling
