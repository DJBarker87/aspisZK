import R1Z.PrivacyPremisesBin
import R1Z.SharedGrammarBridgeBin
import R1Z.QueryScanPrivacyFinal
import R1Z.RomGrammarBin
import R1Z.RomObserverBin

/-! Final conditional privacy statement for the adopted binary format.
The source experiments remain parameters: their operational handoff (including
D46/D51 builder and D75 checker correspondence) is NOT proved by byte grammar.
D80 is consumed at its exact universal quantifiers, including inconsistent
answer vectors. D81 identifies the binary grammar; D79/addendum separation
is exported below on the concrete carrier. See PRIVACY-FINAL-20261020.md. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1Final
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- D80's eight constructor equations, each at the full AddressAt quantifiers. -/
structure RCommitSource (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) : Prop where
  roots : ∀ T, AddressAt W Pr (.inl T)
  mask_expander : ∀ c, AddressAt W Pr (.inr (.inl (.inl c)))
  source_expander : ∀ c, AddressAt W Pr (.inr (.inl (.inr c)))
  bindings : ∀ b, AddressAt W Pr (.inr (.inr (qBind b)))
  seeds : ∀ i, AddressAt W Pr (.inr (.inr (qSeed i)))
  salts : ∀ T u, AddressAt W Pr (.inr (.inr (qSalt T u)))
  leaves : ∀ T u, AddressAt W Pr (.inr (.inr (qLeaf T u)))
  nodes : ∀ T n, AddressAt W Pr (.inr (.inr (qNode T n)))

theorem commit_source (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (s : RCommitSource W Pr) :
    RCommitBytes W Pr :=
  (commit_bytes_iff W Pr).mpr ⟨s.roots, s.mask_expander, s.source_expander,
    s.bindings, s.seeds, s.salts, s.leaves, s.nodes⟩

/-- Normalized per-transaction batches, never the repeated raw leaf-call list. -/
structure RWireBatches (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) where
  fib : Challenges K → Fin 2 → Fin 3 → Finset Fib
  reads : Challenges K → Fin 2 → List (Fin 3 ⊕ RIdx)
  concatenation : ∀ ch, Pr.openList ch = reads ch 0 ++ reads ch 1
  nodup : ∀ ch b, (reads ch b).Nodup
  coverage : ∀ ch b c, c ∈ reads ch b ↔ openedQ (fib ch b) c
  fibre_union : ∀ ch T, Pr.openFib ch T = fib ch 0 T ∪ fib ch 1 T

theorem wire_batches (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (s : RWireBatches W Pr) : ROpen Pr :=
  open_of_batches W Pr s.fib s.reads s.concatenation s.nodup s.coverage s.fibre_union

/-- The shared grammar inherits D79 separation, including all three binding
classes. Execution membership in this concrete carrier is still R-wire. -/
theorem shared_wire_separation (wire : WireLengthsR1PBin.Wire)
    (answers : RIdx → OracleAnswer) (children : Fin 2 → RIdx)
    (read : WireBindingLengthsR1PBin.ExtendedRead) :
    AspisR1.SharedBinaryRecordGrammar.nodeInput (fun j => answers (children j)) ≠
      read.bytes wire := by
  rw [← SharedGrammarBridgeBin.node_eq]
  exact WireBindingLengthsR1PBin.node_ne_extended_read wire answers children read

/-- The exact D52/D77 model error; the ideal programming term is zero. -/
def modelError (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (L₁ L₂ : ℕ) : ℚ :=
  ((8 * n1 W Pr : ℕ) : ℚ) * W.qmax / (2 : ℚ)^255 +
  (((8 * n1 W Pr : ℕ) : ℚ)^2 / (2 : ℚ)^255 +
    εexhP 8 L₁ L₂ (8 * n1 W Pr)) + 0 +
  (8 : ℚ) * (4096 / (((2^31-1)^4-1 : ℕ) : ℚ))

/-- Every numerical slot at the conservative D76 envelope M=2^25,
q=2^64, L1+L2≤49152. Split powers before normalizing. -/
theorem deployed_term_values :
    ((2 : ℚ)^25 * 2^64 / 2^255 = 1 / 2^166) ∧
    (((2 : ℚ)^25)^2 / 2^255 = 1 / 2^205) ∧
    ((8 : ℚ) * (16 * 49152) / 2^496 ≤ 1 / 2^473) ∧
    ((2 : ℚ)^25 / 2^255 = 1 / 2^230) ∧
    ((8 : ℚ) * (4096 / (((2^31-1)^4-1 : ℕ) : ℚ)) ≤
      1 / 2^109 + 1 / 2^138 + 1 / 2^160) ∧
    ((16 : ℚ) / 2^486 ≤ 1 / 2^454) := by
  refine ⟨by norm_num, by norm_num, ?_, by norm_num,
    R1Z.ReadBudgetR1.pole_N8, query_error_le⟩
  rw [show (496 : ℕ) = 248 + 248 from rfl, pow_add,
    show (473 : ℕ) = 230 + 243 from rfl, pow_add]
  norm_num

/-- Exact D77 worst-case count, rather than the conservative power-of-two
read envelope. This equality displays both components of epsilon_exh. -/
theorem deployed_exact_error (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W)
    (hE₁ : Pr.E₁ = 90112) (hE₂ : Pr.E₂ = 8192) (hq : W.qmax = 2^64) :
    modelError W Pr 45056 4096 =
      (19661736 : ℚ) * 2^64 / 2^255 +
      ((19661736 : ℚ)^2 / 2^255 +
        (6291456 / (2 : ℚ)^496 + 19661736 / (2 : ℚ)^255)) + 0 +
      (8 : ℚ) * (4096 / (((2^31-1)^4-1 : ℕ) : ℚ)) := by
  rw [modelError, n1_worst_case W Pr hE₁ hE₂, hq]
  norm_num only [εexhP, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_pow]

section ChosenROM
variable (base : R1Wire K CommitHandle Aux) (publicWidth : ℕ)
local notation "W" => RomFiniteBin.wire base (RomGrammarBin.bound publicWidth)

/-- ONE composed endpoint. The two ScanCoupling hypotheses are the source
handoffs: real includes builder/checker/retry/publication correctness; ideal
includes the Rust sim_e/programmed-oracle correspondence. They permit only
QueryScan disagreement and require its actual reached-history law.
All other Semantic errors must be impossible or agree in those handoffs.
The table backend, query cap and Boolean observer map are constructed here;
the source supplies typed read coverage and its operational query program. -/
theorem privacy_R1_final
    (Pr : R1ProverP K CommitHandle Aux F W)
    (h : HonestProver K) (B : PackBasis F) (hB : R0Z.K4.PackField B)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (hpub : PublicBase F x.1)
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
    (D : SemRows01 W)
    (ι : R1J.SamplerLawSpend.QF → K) (hι : Function.Injective ι)
    (R_wire_Sem1Uniform : D.s1 = R1J.SamplerLawSpend.s1Spend ι)
    (R_wire_read_coverage : RomGrammarBin.ReadCoverage W Pr publicWidth h B outputs x)
    (R_causal_D80 : ∀ (w : h.Instance) sec d p v v', Earlier W Pr p v v' →
      attAddr W Pr h B outputs x w sec d v p = attAddr W Pr h B outputs x w sec d v' p)
    (R_commit_D80 : RCommitSource W Pr) (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer) =>
        Pr.tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh Pr L₁ L₂)
    (R_commit_counter₁ : Pr.E₁ ≤ 2^64) (R_commit_counter₂ : Pr.E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ Pr.E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ Pr.E₂ * 8)
    (R_wire_coin_carrier : (W).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches W Pr)
    (R_wire_D80_ordered_log : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      (W).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (Pr.openList ch).map (fun c =>
          (gram ((W).pubBytes x) (W).vtag (Pr.leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := Pr.E₁) (E₂ := Pr.E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : Pr.E₁ ≤ 2 * L₁) (R_commit_blocks₂ : Pr.E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
      h.public w = x.1 → ScanCoupling
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P W Pr 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ScanCoupling
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P W Pr 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x))) :
    ZK_FSS h B outputs source x (simE h.transport B outputs x)
      (modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486) ∧
    modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 := by
  let R_rom_classical : RomModel W := RomFiniteBin.rom base (RomGrammarBin.bound publicWidth)
  have R_rom_address_domain : ∀ w : h.Instance,
      RAddrIn W Pr R_rom_classical h B outputs x w :=
    RomGrammarBin.address_domain base publicWidth Pr h B outputs x R_wire_read_coverage
  have R_rom_adversary_budget : (W).qmax ≤ 2^64 :=
    RomFiniteBin.adversary_budget base (RomGrammarBin.bound publicWidth)
  have hb := commit_source W Pr R_commit_D80
  have hc : ∀ w : h.Instance, RCausal W Pr h B outputs x w :=
    fun w => (causal_iff W Pr h B outputs x w).mpr (R_causal_D80 w)
  have hop := wire_batches W Pr R_wire_D80_batches
  have hcom := (com_log_iff W Pr hb R_wire_coin_carrier h B outputs x).mpr R_wire_D80_ordered_log
  have hz := R1Z.PrivacyR1PBin.privacy_R1_games' W Pr 8 (by decide) h B hB outputs x
    hpub builder_refinement_D46_D51 D
    (R1J.PrivacySamplerSpend.samplerLaw_of_spend W D ι hι R_wire_Sem1Uniform)
    R_rom_classical R_rom_address_domain hc hb cF R_commit_equal_fibres L₁ L₂
    R_commit_exhaustion R_commit_counter₁ R_commit_counter₂ R_commit_stream₁ R_commit_stream₂
    R_wire_coin_carrier hop hcom
  have hm : ZK_FSS h B outputs (fsR1P W Pr 8 (by decide)
      (P_R1 h.transport B hB) (fun h' => VR1 h')) x
      (simE h.transport B outputs x) (modelError W Pr L₁ L₂) := by
    simpa only [modelError, abR1P, abR1, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_zero, zero_mul, zero_div, pow_two] using hz
  constructor
  · intro adv w hw
    have hr := scan_coupling_le _ _ (R_wire_builder_checker_D75_retry adv w hw)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
    have hi := scan_coupling_le _ _ (G_sim_R_wire adv)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (fun _ => ⟨bit_nonneg _, bit_le_one _⟩)
    have hmid := hm (RomObserverBin.observerMap source observer_program adv) w hw
    have t₁ := abs_sub_le
      (mean (realTest h B outputs source adv x w))
      (mean (realTest h B outputs (fsR1P W Pr 8 (by decide)
        (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w))
      (mean (idealTestS (fsR1P W Pr 8 (by decide)
        (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x
          (simE h.transport B outputs x)))
    have t₂ := abs_sub_le
      (mean (realTest h B outputs source adv x w))
      (mean (idealTestS (fsR1P W Pr 8 (by decide)
        (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x
          (simE h.transport B outputs x)))
      (mean (idealTestS source adv x (simE h.transport B outputs x)))
    rw [abs_sub_comm] at hi
    calc _ ≤ (8 / (2 : ℚ)^486 + modelError W Pr L₁ L₂) + 8 / (2 : ℚ)^486 :=
          t₂.trans (add_le_add (t₁.trans (add_le_add hr hmid)) hi)
         _ = _ := by ring
  · have he := R1Z.PrivacyBoundR1PBin.binary_exhaustion_le W Pr L₁ L₂
      R_commit_cell_count R_commit_blocks₁ R_commit_blocks₂
    have hn := R1Z.GamesR1PBin.binary_games_error_le W Pr L₁ L₂ (W).qmax
      (εexhP 8 L₁ L₂ (8 * n1 W Pr)) R_commit_cell_count R_commit_blocks₁ R_commit_blocks₂
      R_rom_adversary_budget he
    have hn' : modelError W Pr L₁ L₂ ≤ 1 / 2^109 + 1 / 2^137 := by
      simpa only [modelError, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_zero, pow_two, zero_mul, zero_div] using hn
    linarith [query_error_le]

end ChosenROM

#print axioms commit_source
#print axioms wire_batches
#print axioms shared_wire_separation
#print axioms deployed_term_values
#print axioms deployed_exact_error
#print axioms privacy_R1_final
#print axioms R1Z.PrivacySimulatorBin.privacy_R1_eff_binary
end R1Z.PrivacyR1Final
