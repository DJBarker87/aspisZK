import R1Z.SimulatorLogR1PBin
import R1Z.PrivacyBoundR1PBin

/-! ZF2 release root on the adopted Bin chain. The simulator's log is
characterized in SimulatorLogR1PBin. The existing binary root already applies
SimulatorR1.privacy_R1_eff; this exports its D76 budget with that log bridge
in the dependency cone. R-wire/causality/ROM premises remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacySimulatorBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

theorem privacy_R1_eff_binary (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
    (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
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
    (eCm : W.Cm ≃ (RIdx → OracleAnswer)) (hop : ROpen Pr) (hcom : RComLog W Pr eCm h B outputs x)
    (hcount : RCommitCount L₁ L₂) (hb₁ : Pr.E₁ ≤ 2 * L₁) (hb₂ : Pr.E₂ ≤ 2 * L₂)
    (hq : W.qmax ≤ 2 ^ 64) :
    ZK_FSS h B outputs (fsR1P W Pr 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h')) x
      (simE h.transport B outputs x)
      (1 / 2 ^ 109 + 1 / 2 ^ 137) := by
  have hz := privacy_R1_eff h B hB outputs
    (fsR1P W Pr 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h')) x
    hpub hs (abR1P W 8 (by decide)) (8 * n1 W Pr) 0 W.qmax (2 ^ 255)
    ((2 ^ 31 - 1) ^ 4 - 1) (εexhP 8 L₁ L₂ (8 * n1 W Pr)) (by positivity)
    (realModel_R1P W Pr R eCm 8 (by decide) (P_R1 h.transport B hB)
      (fun h' => VR1 h') h (VR1 h) B outputs x hin hc hb hop hcom
      (fun _ _ => Iff.rfl) cF hfib hE₁ hE₂ L₁ L₂ hex h₁ h₂)
    (R1Z.PrivacyR1PBin.idealModelS_R1P W Pr 8 (by decide) _ _ x 0 (2 ^ 255)
      (simE h.transport B outputs x))
    (fun adv => sem1Uniform_abR1 W 8 (by decide) D
      (R1J.PrivacySamplerSpend.samplerLaw_of_spend W D ι hι hD) adv x)
  intro adv w hw
  refine (hz adv w hw).trans ?_
  simpa only [abR1P, abR1, Nat.cast_ofNat] using
    (binary_games_error_le W Pr L₁ L₂ W.qmax (εexhP 8 L₁ L₂ (8 * n1 W Pr))
      hcount hb₁ hb₂ hq
      (R1Z.PrivacyBoundR1PBin.binary_exhaustion_le W Pr L₁ L₂ hcount hb₁ hb₂))

#print axioms privacy_R1_eff_binary
end R1Z.PrivacySimulatorBin
