import R1Z.PrivacyGamesSamplerR1
import R1Z.SamplerLawBridge
import R1J.SamplerLawSpend

/-! (c) end to end on the unified base (LOG D65 follow-up): the `QM31SamplerLaw` premise of
`privacy_R1_games_sampler` discharged in one closure by the spend path's extracted sampler,
`R1J.SamplerLawSpend.qm31SamplerLaw_spend` → `R1Z.SamplerLawBridge.toSem1`.

What remains a premise: `SemRows01 W` (the wire decoder reads χ = sem 1 from row 1 through
`s1`, and λ = sem 0 not from row 1), here with its `s1` fixed to `s1Spend ι` for an injective
`ι : QM31Exact → K` (the QM31 ↔ K carrier map), and the hypotheses of `privacy_R1_games`. -/
set_option autoImplicit false
noncomputable section
namespace R1J.PrivacySamplerSpend
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.PrivacyGamesR1 R1Z.PrivacyGamesSamplerR1
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- The sampler law for the wire's row-1 map, when that map is the spend path's extracted
`qm31_sample` read through an injective carrier map. -/
def samplerLaw_of_spend (W : R1Wire K CommitHandle Aux) (D : SemRows01 W)
    (ι : R1J.SamplerLawSpend.QF → K) (hι : Function.Injective ι)
    (hD : D.s1 = R1J.SamplerLawSpend.s1Spend ι) : QM31SamplerLaw D.s1 := by
  rw [hD]
  exact R1Z.SamplerLawBridge.toSem1 (R1J.SamplerLawSpend.qm31SamplerLaw_spend ι hι)

/-- `privacy_R1_games_sampler` with `QM31SamplerLaw` discharged by the extracted sampler. -/
theorem privacy_R1_games_spendSampler (W : R1Wire K CommitHandle Aux)
    (Pr : R1Prover K CommitHandle Aux F W)
    (N : ℕ) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x) (Mc : ℕ) (εexh : ℚ)
    (hd : ∀ (adv : R1Adv K CommitHandle Aux) (w : h.Instance), h.public w = x.1 →
      ∃ d : R1RealData W Pr N hN (P_R1 h.transport B hB) (fun h' => VR1 h') h (VR1 h) B outputs x
          adv w Mc,
        d.Agree ∧ R0Z.FsAbortBounds.mass d.exh ≤ εexh)
    (D : SemRows01 W) (ι : R1J.SamplerLawSpend.QF → K) (hι : Function.Injective ι)
    (hD : D.s1 = R1J.SamplerLawSpend.s1Spend ι) :
    ZK_FSS h B outputs (fsR1 W Pr N hN (P_R1 h.transport B hB) (fun h' => VR1 h')) x
      (simE h.transport B outputs x)
      (((N * (115 + Mc) : ℕ) : ℚ) * (W.qmax : ℕ) / ((2 ^ 255 : ℕ) : ℚ) +
        (((N * (115 + Mc) : ℕ) : ℚ) * ((N * (115 + Mc) : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) + εexh) +
        ((0 : ℕ) : ℚ) * ((0 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (abR1 W N hN).N * ((4096 : ℚ) / (((2 ^ 31 - 1) ^ 4 - 1 : ℕ) : ℚ))) :=
  privacy_R1_games_sampler W Pr N hN h B hB outputs x hpub hs Mc εexh hd D
    (samplerLaw_of_spend W D ι hι hD)

end R1J.PrivacySamplerSpend

#print axioms R1J.PrivacySamplerSpend.samplerLaw_of_spend
#print axioms R1J.PrivacySamplerSpend.privacy_R1_games_spendSampler
