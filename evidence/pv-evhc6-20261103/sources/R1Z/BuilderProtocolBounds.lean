import R1Z.PrivacyR1FinalProtocol

set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderProtocolBounds
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final
local notation "K" => AspisWideTower.WideExact
variable {CommitHandle Aux : Type} {F : Subfield K}
variable (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
variable (seed : R1ProverP K CommitHandle Aux F (wire base publicWidth h B outputs x).toWire)

/-- The numerical protocol envelope does not require public base membership,
a witness, builder soundness or a source execution coupling. -/
theorem error_bound (L₁ L₂ : ℕ)
    (hc : RCommitCount L₁ L₂)
    (hb₁ : (prover base publicWidth h B outputs x seed).toProver.E₁ ≤ 2 * L₁)
    (hb₂ : (prover base publicWidth h B outputs x seed).toProver.E₂ ≤ 2 * L₂) :
    modelError (wire base publicWidth h B outputs x).toWire
      (prover base publicWidth h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 := by
  let W := (wire base publicWidth h B outputs x).toWire
  let Pr := (prover base publicWidth h B outputs x seed).toProver
  have he := R1Z.PrivacyBoundR1PBin.binary_exhaustion_le W Pr L₁ L₂ hc hb₁ hb₂
  have hq : W.qmax ≤ 2^64 := Nat.le_refl _
  have hn := R1Z.GamesR1PBin.binary_games_error_le W Pr L₁ L₂ W.qmax
    (εexhP 8 L₁ L₂ (8 * n1 W Pr)) hc hb₁ hb₂ hq he
  have hn' : modelError W Pr L₁ L₂ ≤ 1 / 2^109 + 1 / 2^137 := by
    simpa only [modelError, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_zero, pow_two,
      zero_mul, zero_div] using hn
  change modelError W Pr L₁ L₂ + _ ≤ _
  linarith [query_error_le]

#print axioms error_bound
end R1Z.BuilderProtocolBounds
