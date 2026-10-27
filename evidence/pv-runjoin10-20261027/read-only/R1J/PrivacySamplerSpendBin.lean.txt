import R1Z.PrivacyR1PBin
import R1J.PrivacySamplerSpend

/-! Binary phase-indexed root with the extracted spend sampler law. -/
set_option autoImplicit false
noncomputable section
namespace R1J.PrivacySamplerSpendBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}


theorem privacy_R1_games_spendSampler_bin (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
    (N : ℕ) (hN : 0 < N) (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (hs : R0Z.HonestValidity.BuilderSoundOn h B x)
    (D : SemRows01 W)
    (ι : R1J.SamplerLawSpend.QF → K) (hι : Function.Injective ι)
    (hD : D.s1 = R1J.SamplerLawSpend.s1Spend ι)
    (R : RomModel W) (hin : ∀ w : h.Instance, RAddrIn W Pr R h B outputs x w)
    (hc : ∀ w : h.Instance, RCausal W Pr h B outputs x w)
    (hb : RCommitBytes W Pr) (cF : ℕ)
    (hfib : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        Pr.tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (hex : RExh Pr L₁ L₂) (hE₁ : Pr.E₁ ≤ 2 ^ 64) (hE₂ : Pr.E₂ ≤ 2 ^ 64)
    (h₁ : 16 * L₁ ≤ Pr.E₁ * 8) (h₂ : 16 * L₂ ≤ Pr.E₂ * 8)
    (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (hop : ROpen Pr) (hcom : RComLog W Pr eCm h B outputs x) :
    ZK_FSS h B outputs (fsR1P W Pr N hN (P_R1 h.transport B hB) (fun h' => VR1 h')) x
      (simE h.transport B outputs x)
      (((N * n1 W Pr : ℕ) : ℚ) * (W.qmax : ℕ) / ((2 ^ 255 : ℕ) : ℚ) +
        (((N * n1 W Pr : ℕ) : ℚ) * ((N * n1 W Pr : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
          εexhP N L₁ L₂ (N * n1 W Pr)) +
        ((0 : ℕ) : ℚ) * ((0 : ℕ) : ℚ) / ((2 ^ 255 : ℕ) : ℚ) +
        (abR1P W N hN).N * ((4096 : ℚ) / (((2 ^ 31 - 1) ^ 4 - 1 : ℕ) : ℚ))) :=
  R1Z.PrivacyR1PBin.privacy_R1_games' W Pr N hN h B hB outputs x hpub hs D
    (R1J.PrivacySamplerSpend.samplerLaw_of_spend W D ι hι hD) R hin hc hb cF hfib
    L₁ L₂ hex hE₁ hE₂ h₁ h₂ eCm hop hcom

#print axioms privacy_R1_games_spendSampler_bin
end R1J.PrivacySamplerSpendBin
