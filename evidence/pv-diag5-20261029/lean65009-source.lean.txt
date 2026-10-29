import R1Z.ProverCommitDeployedFuel22
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineDeployedReal
abbrev ownedDecode := ProverCommitOwnedDecoder.decoder (K := PrivacyR1AcctBasis.K)
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.ProverCommitTapeCompletion
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit
open R1Z.PrivacyR1Headline
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
local notation "hB" => PrivacyR1AcctBasis.packing_laws
local notation "L₁" => PrivacyR1AcctModel.L₁
local notation "L₂" => PrivacyR1AcctModel.L₂
attribute [local irreducible] ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux)

local notation "log" => PhaseWireLog2Bin.log
local notation "base" => PrivacyR1AcctModel.base template log
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective
    AspisCircleGroupOrder.P

def input : HonestProver K := BuilderSource.prover

variable (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
local notation "h" => PhaseWireLog2Bin.honest input
local notation "decode" => ownedDecode

local notation "fib" => PhaseWireLog2Bin.fib
local notation "opens" => PhaseWireLog2Bin.opens
local notation "seed" => PrivacyR1AcctModel.seed
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) decode fib opens
open R1Z.PrivacyR1HeadlineWire2
local notation "raw" => fsR1P
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x))
  (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed))
  8 eight_pos (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
local notation "coins" => PrivacyR1AcctModel.wire_coins template log h outputs x
local notation "W" => R1Z.PhaseLocalityBin.R1PhaseWire.toWire
  (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)
local notation "Pr" => R1Z.PhaseLocalityBin.R1PhaseProver.toProver
  (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)

local notation "source" => ProverCommitReencode16.experiment W Pr 8 eight_pos
  (P_R1 (R0Z.ZkStatement.HonestProver.transport h) B hB) (fun h' => VR1 h')
  ProverCommitReencode16.encode

variable (rust : FSExperiments K CommitHandle Aux R1Bat F)
  [Fintype rust.RealRand] [Nonempty rust.RealRand]
  (observer_program : rust.Adversary → View K CommitHandle Aux R1Bat →
    List (List UInt8 × OracleAnswer) → OProg)

/-- Exact adversary-only query suffix of the underlying ordered source. -/
def realSeedQueries (adv : rust.Adversary) (w : (h).Instance) : (source).RealRand →
    List ProverCommitSeedEvent19.Entry :=
  ProverCommitObserverQueries19.real W Pr 8
    (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs
    (ProverCommitReencode16.observer ProverCommitReencode16.encode
      (RomObserverBin.observerMap rust observer_program adv)) x w

def RustRealRefinement : Prop :=
  ∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))

attribute [local irreducible] PrivacyR1AcctBasis.basis
theorem privacy_headline_deployed
    (refinement : RustRealRefinement template outputs x rust observer_program)
 :
    (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
      |mean (realTest h B outputs rust adv x w) -
        mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
          (simE (h).transport B outputs x))| ≤
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100 := by
  have model := PrivacyR1HeadlineOwnedClosed.Admitted.FixedObserver.privacy_headline_admitted
    template outputs x
  have caller := ProverCommitOwnedEndpoint.caller_law template input outputs x
  obtain ⟨hc₁,hc₂,hs₁,hs₂,hcount,hb₁,hb₂⟩ := ProverCommitCallerInstance.budgets Pr caller
  have hM := ProverCommitModelCore16.read_bound W Pr L₁ L₂ hcount hb₁ hb₂
  have hk := QueryScanFreshNumerics.lazy_budget_le_fresh hM
    (Nat.succ_le_succ (Nat.zero_le (8 * n1 W Pr)))
  constructor
  · intro adv w hw
    have hr₀ := ProverCommitFuelJoin22.test_bound
      (Classical.choice (refinement adv w hw)) (fun run => bit run.2)
      (fun _ => ⟨bit_nonneg _, bit_le_one _⟩) (2^64)
      (fun r => ProverCommitObserverQueries19.real_bound W Pr 8
        (P_R1 (h).transport B hB) (fun h' => VR1 h') h B outputs _ x w r)
    have hscan : 8 * scanProbability ≤ 8 / (2 : ℚ)^486 := by
      simpa only [mul_one_div] using
        mul_le_mul_of_nonneg_left scan_probability_le (by norm_num : (0 : ℚ) ≤ 8)
    have hr := hr₀.trans (add_le_add (add_le_add
      ((ProverCommitModelCore16.real_bad_mass base h B outputs x seed hc₁ hc₂ w).trans
        (add_le_add (le_refl _) hscan)) (le_refl (ProverCommitSeedEvent19.budget (2^64)))) (le_refl ProverCommitFuelMass22.charge))
    obtain ⟨hpub, hs⟩ := PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises (x := x) w hw
    have core := ProverCommitModelCore16.core_privacy base h B outputs x seed hB hpub hs
      ProverCommitSourceDecoder.quotientFibreSize (by
        intro τ
        convert ProverCommitCallerInstance.fibres Pr caller τ using 2
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])
      L₁ L₂ (ProverCommitCallerInstance.exhaustion Pr caller)
      hc₁ hc₂ hs₁ hs₂ coins
      (PhaseWireLog2Bin.batches input outputs x template decode)
      (PhaseWireLog2Bin.ordered_log input outputs x template decode) hcount hb₁ hb₂
    have mid := ProverCommitReencode16.privacy_transport _ _ _ _ _ _
      ProverCommitReencode16.encode _ _ _ _ _ core
    have hmid := mid (RomObserverBin.observerMap rust observer_program adv) w hw
    have t₁ := abs_sub_le
      (mean (realTest h B outputs rust adv x w))
      (mean (realTest h B outputs source (RomObserverBin.observerMap rust observer_program adv) x w))
      (mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
        (simE (h).transport B outputs x)))
    have spare : (0 : ℚ) ≤ 8 / (2 : ℚ)^486 +
        ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge := by
      unfold ProverCommitSeedEvent19.budget ProverCommitFuelMass22.charge
      positivity
    calc _ ≤ (QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486 +
          ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge) +
          modelError W Pr L₁ L₂ := t₁.trans (add_le_add hr hmid)
         _ ≤ ((QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) + 8 / (2 : ℚ)^486 +
          ProverCommitSeedEvent19.budget (2^64) + ProverCommitFuelMass22.charge) +
          modelError W Pr L₁ L₂) +
          (8 / (2 : ℚ)^486 + ProverCommitSeedEvent19.budget (2^64) +
          ProverCommitFuelMass22.charge) := le_add_of_nonneg_right spare
         _ = modelError W Pr L₁ L₂ + 16 / (2 : ℚ)^486 +
           QueryScanRealLazyBound.lazyBudget (8 * n1 W Pr) +
           2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge := by ring
         _ ≤ _ := add_le_add (add_le_add (add_le_add (le_refl _) hk) (le_refl _)) (le_refl _)

  · constructor
    · exact add_le_add (add_le_add model.2.1 (le_refl _)) (le_refl _)
    · apply (add_le_add (add_le_add model.2.1 (le_refl _)) (le_refl _)).trans_lt
      exact ProverCommitFuelMass22.total_lt_target
        (Nat.le_trans (Nat.add_le_add_right hM 1) (by norm_num)) (Nat.le_refl _)

/-- The original two-conjunct certificate implies the new endpoint's only
refinement premise. The second conjunct is unused. -/
theorem old_refinement_implies
    [Fintype rust.IdealRand] [Nonempty rust.IdealRand]
    (old : ProverCommitDeployedFuel22.RustProverRefinement
      template outputs x rust observer_program) :
    RustRealRefinement template outputs x rust observer_program := old.1

#print axioms privacy_headline_deployed
#print axioms old_refinement_implies
end R1Z.PrivacyR1HeadlineDeployedReal
