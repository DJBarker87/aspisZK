import R1Z.SimulatorR1
import R1Z.GamesR1

/-! R1 games (zf1/DESIGN-R1-GAMES §6): `privacy_R1_eff` (LOG D44) instantiated
with the concrete R1 experiments `fsR1` and bridge `abR1`.  The ideal model
`R1IdealModelS … simE` is a theorem (`idealModelS_R1`, with no private
position, so the programming term is 0); the real model comes from
`realModel_R1`, whose remaining inputs are the `R1RealData` hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyGamesR1
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- `R1IdealModelS` for the R1 games and any simulator (in particular `simE`). -/
theorem idealModelS_R1 (W : R1Wire K CommitHandle Aux) (Pr : R1Prover K CommitHandle Aux F W)
    (N : ℕ) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop) (x : Statement K CommitHandle)
    (M Umin : ℕ) (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat) :
    R1IdealModelS P (fsR1 W Pr N hN P Vp) (abR1 W N hN) x M Umin sim :=
  fun adv => idealModelS_body W Pr N hN P Vp x M Umin sim adv

/-- The R1 privacy theorem for the concrete games against the explicit
simulator `simE`: error `N(115+Mc)·q/2^255 + (N(115+Mc))²/2^255 + εexh +
N·4096/Q`; the ideal (programming) term is 0. -/
theorem privacy_R1_games (W : R1Wire K CommitHandle Aux) (Pr : R1Prover K CommitHandle Aux F W)
    (N : ℕ) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x) (Mc Q : ℕ) (εexh : ℚ)
    (hd : ∀ (adv : R1Adv K CommitHandle Aux) (w : h.Instance), h.public w = x.1 →
      ∃ d : R1RealData W Pr N hN (P_R1 h.transport B hB) (fun h' => VR1 h') h (VR1 h) B outputs x
          adv w Mc,
        d.Agree ∧ R0Z.FsAbortBounds.mass d.exh ≤ εexh)
    (hdraw : Sem1Uniform (drawW (K := K) W) Q) :
    ZK_FSS h B outputs (fsR1 W Pr N hN (P_R1 h.transport B hB) (fun h' => VR1 h')) x
      (simE h.transport B outputs x)
      (((N * (115 + Mc) : ℕ) : ℚ) * (W.qmax : ℕ) / ((2 ^ 255 : ℕ) : ℚ) +
        (((N * (115 + Mc) : ℕ) : ℚ) * ((N * (115 + Mc) : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) + εexh) +
        ((0 : ℕ) : ℚ) * ((0 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (abR1 W N hN).N * ((4096 : ℚ) / Q)) :=
  privacy_R1_eff h B hB outputs (fsR1 W Pr N hN (P_R1 h.transport B hB) (fun h' => VR1 h')) x
    hpub hs (abR1 W N hN) (N * (115 + Mc)) 0 W.qmax (2 ^ 255) Q εexh (by positivity)
    (realModel_R1 Mc εexh hd)
    (idealModelS_R1 W Pr N hN _ _ x 0 (2 ^ 255) (simE h.transport B outputs x))
    (fun _ => hdraw)

#print axioms idealModelS_R1
#print axioms privacy_R1_games
end R1Z.PrivacyGamesR1
