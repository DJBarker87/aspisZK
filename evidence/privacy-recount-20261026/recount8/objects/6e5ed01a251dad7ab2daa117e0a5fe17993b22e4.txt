import R1J.PrivacySamplerSpendBin
import R1Z.LayoutCountR1PBin
import R1Z.LayoutObstructionR1PBin

/-! D76 bound for the binary phase-indexed root, including both binding reads. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyBoundR1PBin
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1
attribute [local instance] Classical.propDecidable

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

theorem binary_exhaustion_le (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (L₁ L₂ : ℕ)
    (hc : RCommitCount L₁ L₂) (h₁ : Pr.E₁ ≤ 2 * L₁) (h₂ : Pr.E₂ ≤ 2 * L₂) :
    εexhP 8 L₁ L₂ (8 * n1 W Pr) ≤ 1 / 2 ^ 229 := by
  have hm : ((8 * n1 W Pr : ℕ) : ℚ) ≤ 2 ^ 25 := by
    have h := n1_le W Pr L₁ L₂ hc h₁ h₂
    have hh : 8 * n1 W Pr ≤ 2 ^ 25 := by norm_num at h ⊢; omega
    exact_mod_cast hh
  have hl : (16 * (L₁ + L₂) : ℚ) ≤ 2 ^ 20 := by
    obtain ⟨hL₁, hL₂⟩ := hc
    have hh : 16 * (L₁ + L₂) ≤ 2 ^ 20 := by norm_num at hL₁ hL₂ ⊢; omega
    exact_mod_cast hh
  have he : (8 : ℚ) * 2 ^ 20 / 2 ^ 496 ≤ 1 / 2 ^ 230 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ 496)
      (by positivity : (0 : ℚ) < 2 ^ 230)).mpr
    rw [one_mul, show (8 : ℚ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hb : (2 : ℚ) ^ 25 * (1 / 2 ^ 255) = 1 / 2 ^ 230 := by
    rw [show (255 : ℕ) = 25 + 230 from rfl, pow_add]
    field_simp
  unfold εexhP
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ (8 : ℚ) * 2 ^ 20 / 2 ^ 496 + 2 ^ 25 * (1 / 2 ^ 255) :=
      add_le_add
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num))
          (by positivity))
        (mul_le_mul_of_nonneg_right hm (by positivity))
    _ ≤ 1 / 2 ^ 230 + 1 / 2 ^ 230 := add_le_add he (le_of_eq hb)
    _ ≤ 1 / 2 ^ 229 := by norm_num

#print axioms binary_exhaustion_le

theorem privacy_R1_games_binary_bound (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
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
  have hz := R1J.PrivacySamplerSpendBin.privacy_R1_games_spendSampler_bin
    W Pr 8 (by decide) h B hB outputs x hpub hs D ι hι hD R hin hc hb cF hfib
    L₁ L₂ hex hE₁ hE₂ h₁ h₂ eCm hop hcom
  intro adv w hw
  refine (hz adv w hw).trans ?_
  simpa only [abR1P, abR1, Nat.cast_ofNat] using
    (binary_games_error_le W Pr L₁ L₂ W.qmax (εexhP 8 L₁ L₂ (8 * n1 W Pr))
      hcount hb₁ hb₂ hq (binary_exhaustion_le W Pr L₁ L₂ hcount hb₁ hb₂))

#print axioms privacy_R1_games_binary_bound
end R1Z.PrivacyBoundR1PBin
