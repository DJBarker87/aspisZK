import R1Z.PrivacyR1Final
import R1Z.PhaseProtocolCoverageBin

/-! Release privacy endpoint over the constructed phase protocol model.
Source experiments and the residual tape/opening data retain their explicit
handoffs; no Rust execution identification is inferred. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1FinalProtocol
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

/-- The eight address families are selected by the phase prover constructor. -/
theorem commitment_grammar :
    PrivacyR1Final.RCommitSource (wire base publicWidth h B outputs x).toWire (prover base publicWidth h B outputs x seed).toProver := by
  constructor <;> intros <;> unfold AddressAt <;> intros <;> rfl

/-- Release specialization with the ROM width chosen as the public byte
length. Sampler, grammar, universal causality and typed read coverage are
constructed. All residual premises keep their original quantifiers. -/
theorem privacy_R1_protocol
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
      h.public w = x.1 → ScanCoupling
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ScanCoupling
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x))) :
    ZK_FSS h B outputs source x (simE h.transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 := by
  exact PrivacyR1Final.privacy_R1_final (baseWire base) ((base.pubBytes x).length) (prover base ((base.pubBytes x).length) h B outputs x seed).toProver h B hB outputs x
    hpub builder_refinement_D46_D51 (rows01 base ((base.pubBytes x).length) h B outputs x)
    (algebraMap R1J.SamplerLawSpend.QF K) (RingHom.injective _)
    (sampler_source base ((base.pubBytes x).length) h B outputs x)
    (PhaseProtocolCoverageBin.read_coverage base ((base.pubBytes x).length) h B outputs x seed (Nat.le_refl _))
    (causal_premise base ((base.pubBytes x).length) h B outputs x seed)
    (commitment_grammar base ((base.pubBytes x).length) h B outputs x seed) cF (by
      intro τ
      convert R_commit_equal_fibres τ using 2
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    L₁ L₂ R_commit_exhaustion R_commit_counter₁ R_commit_counter₂
    R_commit_stream₁ R_commit_stream₂ R_wire_coin_carrier R_wire_D80_batches
    R_wire_D80_ordered_log R_commit_cell_count R_commit_blocks₁ R_commit_blocks₂
    source observer_program R_wire_builder_checker_D75_retry G_sim_R_wire

#print axioms commitment_grammar
#print axioms privacy_R1_protocol
end R1Z.PrivacyR1FinalProtocol
