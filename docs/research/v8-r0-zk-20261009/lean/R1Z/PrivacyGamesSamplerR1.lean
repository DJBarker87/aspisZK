import R1Z.Sem1UniformR1
import R1Z.PrivacyGamesR1

/-! `privacy_R1_games` with its `Sem1Uniform` hypothesis discharged by
`sem1Uniform_drawW`: the `hdraw` premise is replaced by the wire facts
`SemRows01 W` and `QM31SamplerLaw`, and `Q = p⁴ − 1`.  The landed theorem is
unchanged; this is a new corollary. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyGamesSamplerR1
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.PrivacyGamesR1
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- The R1 privacy theorem for the concrete games against `simE`, with the
sampler premise discharged: error `N(115+Mc)·q/2^255 + (N(115+Mc))²/2^255 +
εexh + N·4096/(p⁴ − 1)`. -/
theorem privacy_R1_games_sampler (W : R1Wire K CommitHandle Aux)
    (Pr : R1Prover K CommitHandle Aux F W)
    (N : ℕ) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x) (Mc : ℕ) (εexh : ℚ)
    (hd : ∀ (adv : R1Adv K CommitHandle Aux) (w : h.Instance), h.public w = x.1 →
      ∃ d : R1RealData W Pr N hN (P_R1 h.transport B hB) (fun h' => VR1 h') h (VR1 h) B outputs x
          adv w Mc,
        d.Agree ∧ R0Z.FsAbortBounds.mass d.exh ≤ εexh)
    (D : SemRows01 W) (L : QM31SamplerLaw D.s1) :
    ZK_FSS h B outputs (fsR1 W Pr N hN (P_R1 h.transport B hB) (fun h' => VR1 h')) x
      (simE h.transport B outputs x)
      (((N * (115 + Mc) : ℕ) : ℚ) * (W.qmax : ℕ) / ((2 ^ 255 : ℕ) : ℚ) +
        (((N * (115 + Mc) : ℕ) : ℚ) * ((N * (115 + Mc) : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) + εexh) +
        ((0 : ℕ) : ℚ) * ((0 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (abR1 W N hN).N * ((4096 : ℚ) / (((2 ^ 31 - 1) ^ 4 - 1 : ℕ) : ℚ))) :=
  privacy_R1_games W Pr N hN h B hB outputs x hpub hs Mc ((2 ^ 31 - 1) ^ 4 - 1) εexh hd
    (sem1Uniform_drawW W D L)

#print axioms privacy_R1_games_sampler
end R1Z.PrivacyGamesSamplerR1
