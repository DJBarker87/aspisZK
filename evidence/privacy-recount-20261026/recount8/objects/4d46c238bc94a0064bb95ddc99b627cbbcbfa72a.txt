import R1Z.ProverCommitQuotientPrivacy
import R1Z.PrivacyR1FinalProtocolHistoryReal
import R1Z.PrivacyR1FinalProtocolHistory
import R1Z.QueryScanFreshNumerics

/-! Real-law-free endpoint with a proved scan-freshness numerical allowance.
The conservative internal coupling budget is dominated by that allowance. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1FinalProtocolQuotient
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.ProverCommitTapeCompletion
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit
local notation "K" => AspisWideTower.WideExact
variable {CommitHandle Aux : Type} {F : Subfield K}
variable (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
theorem privacy_R1_protocol_quotient_of_lazy_budget
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
    (cF : ℕ)
    (R_commit_quotient_fibres : ∀ τ : SourceTape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        quotientDecode (fun e => ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2) e = some τ)).card = cF)
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
      h.public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE h.transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanRealLazyBound.lazyBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanRealLazyBound.lazyBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanRealLazyBound.lazyBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanRealLazyBound.lazyBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver) < 1 / 2^100 := by
  let W := (wire base ((base.pubBytes x).length) h B outputs x).toWire
  let Pr := (prover base ((base.pubBytes x).length) h B outputs x seed).toProver
  let R : RomModel W := RomFiniteBin.rom (baseWire base) (RomGrammarBin.bound ((base.pubBytes x).length))
  have hin : ∀ w : h.Instance, RAddrIn W Pr R h B outputs x w :=
    RomGrammarBin.address_domain (baseWire base) _ Pr h B outputs x
      (PhaseProtocolCoverageBin.read_coverage base _ h B outputs x seed (Nat.le_refl _))
  have hc : ∀ w : h.Instance, RCausal W Pr h B outputs x w :=
    fun w => (causal_iff W Pr h B outputs x w).mpr
      (causal_premise base _ h B outputs x seed w)
  have hb : RCommitBytes W Pr := PrivacyR1Final.commit_source W Pr
    (PrivacyR1FinalProtocol.commitment_grammar base _ h B outputs x seed)
  have hop := PrivacyR1Final.wire_batches W Pr R_wire_D80_batches
  have hcom := (com_log_iff W Pr hb R_wire_coin_carrier h B outputs x).mpr R_wire_D80_ordered_log
  have hz := R1Z.ProverCommitQuotientPrivacy.privacy_R1_games_quotient W Pr 8 (by decide) h B hB outputs x
    hpub builder_refinement_D46_D51 (rows01 base _ h B outputs x)
    (R1J.PrivacySamplerSpend.samplerLaw_of_spend W (rows01 base _ h B outputs x)
      (algebraMap R1J.SamplerLawSpend.QF K) (RingHom.injective _)
      (sampler_source base _ h B outputs x))
    R hin hc hb cF (by
      intro τ
      convert R_commit_quotient_fibres τ using 2
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rfl) L₁ L₂ R_commit_exhaustion
    R_commit_counter₁ R_commit_counter₂ R_commit_stream₁ R_commit_stream₂
    R_wire_coin_carrier hop hcom
  have hm : ZK_FSS h B outputs (fsR1P W Pr 8 (by decide)
      (P_R1 h.transport B hB) (fun h' => VR1 h')) x
      (simE h.transport B outputs x) (modelError W Pr L₁ L₂) := by
    simpa only [modelError, abR1P, abR1, Nat.cast_ofNat, Nat.cast_pow,
      Nat.cast_zero, zero_mul, zero_div, pow_two] using hz
  have he := R1Z.PrivacyBoundR1PBin.binary_exhaustion_le W Pr L₁ L₂
    R_commit_cell_count R_commit_blocks₁ R_commit_blocks₂
  have hn := R1Z.GamesR1PBin.binary_games_error_le W Pr L₁ L₂ W.qmax
    (εexhP 8 L₁ L₂ (8 * n1 W Pr)) R_commit_cell_count R_commit_blocks₁ R_commit_blocks₂
    (RomFiniteBin.adversary_budget (baseWire base) _) he
  have hn' : modelError W Pr L₁ L₂ ≤ 1 / 2^109 + 1 / 2^137 := by
    simpa only [modelError, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_zero,
      pow_two, zero_mul, zero_div] using hn
  constructor
  · intro adv w hw
    have hr := QueryScanRealLazyJoin.join_le _ _ _
      (R_wire_builder_checker_D75_retry adv w hw)
      (QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr))
      (QueryScanRealLazyBound.real_bad_union_mass W Pr R 8 (by decide) h B outputs x w
        (hin w) (hc w) hb R_commit_counter₁ R_commit_counter₂)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
    have hi := scan_coupling_le _ _
      ((G_sim_R_wire adv).toScanCoupling (fun i => QueryScanIdealHistory.selected_bad_mass i))
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
    have hmid := hm (RomObserverBin.observerMap source observer_program adv) w hw
    have t₁ := abs_sub_le
      (mean (realTest h B outputs source adv x w))
      (mean (realTest h B outputs (fsR1P W Pr 8 (by decide)
        (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x w))
      (mean (idealTestS (fsR1P W Pr 8 (by decide)
        (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)))
    have t₂ := abs_sub_le
      (mean (realTest h B outputs source adv x w))
      (mean (idealTestS (fsR1P W Pr 8 (by decide)
        (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)))
      (mean (idealTestS source adv x (simE h.transport B outputs x)))
    rw [abs_sub_comm] at hi
    calc _ ≤ ((QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486) +
        modelError W Pr L₁ L₂) + 8 / (2 : ℚ)^486 :=
          t₂.trans (add_le_add (t₁.trans (add_le_add hr hmid)) hi)
         _ = _ := QueryScanFreshNumerics.amount_identity _ _ _
  · have hbase : modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 ≤
        1 / 2^109 + 1 / 2^137 + 1 / 2^454 := (add_le_add hn' query_error_le)
    have hcount := R1Z.GamesR1PBin.n1_le W Pr L₁ L₂
      R_commit_cell_count R_commit_blocks₁ R_commit_blocks₂
    have hM : 8 * n1 W Pr ≤ 2^25 := by norm_num at hcount ⊢; omega
    have hκ := QueryScanRealLazyJoin.lazy_budget_small hM
    have htotal := add_le_add hbase (le_refl (QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr)))
    exact ⟨htotal, htotal.trans_lt (QueryScanHistoryRealNumerics.total_lt_target
      (QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr)) hκ)⟩

#print axioms privacy_R1_protocol_quotient_of_lazy_budget

theorem privacy_R1_protocol_quotient
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
    (cF : ℕ)
    (R_commit_quotient_fibres : ∀ τ : SourceTape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        quotientDecode (fun e => ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2) e = some τ)).card = cF)
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
      h.public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE h.transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1)) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) < 1 / 2^100 := by
  let W := (wire base ((base.pubBytes x).length) h B outputs x).toWire
  let Pr := (prover base ((base.pubBytes x).length) h B outputs x seed).toProver
  have hz := privacy_R1_protocol_quotient_of_lazy_budget base h B outputs x seed hB hpub
    builder_refinement_D46_D51 cF R_commit_quotient_fibres L₁ L₂ R_commit_exhaustion
    R_commit_counter₁ R_commit_counter₂ R_commit_stream₁ R_commit_stream₂
    R_wire_coin_carrier R_wire_D80_batches R_wire_D80_ordered_log R_commit_cell_count
    R_commit_blocks₁ R_commit_blocks₂ source observer_program
    R_wire_builder_checker_D75_retry G_sim_R_wire
  have hcount := R1Z.GamesR1PBin.n1_le W Pr L₁ L₂
    R_commit_cell_count R_commit_blocks₁ R_commit_blocks₂
  have hM : 8 * n1 W Pr ≤ 2^25 := by norm_num at hcount ⊢; omega
  have hq : 8 * n1 W Pr + 1 ≤ 2^65 := by norm_num at hM ⊢; omega
  have hκ := QueryScanFreshNumerics.lazy_budget_le_fresh hM
    (Nat.succ_le_succ (Nat.zero_le (8 * n1 W Pr)))
  have hinc := add_le_add (le_refl (modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486)) hκ
  have hbase : modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 := le_of_add_le_add_right hz.2.1
  have htotal := add_le_add hbase
    (le_refl (QueryScanFreshUnion.freshBudget (8 * n1 W Pr + 1)))
  exact ⟨(fun adv w hw => (hz.1 adv w hw).trans hinc), htotal,
    htotal.trans_lt (QueryScanFreshNumerics.fresh_total_lt_target hq)⟩

#print axioms privacy_R1_protocol_quotient
end R1Z.PrivacyR1FinalProtocolQuotient
