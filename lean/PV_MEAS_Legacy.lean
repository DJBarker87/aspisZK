import R1Z.ProverCommitDeployedFuel22
import PV_MEAS_Deployed
import PV_MEAS_Finite
import PV_EVH_Deployed
import PV_EVH_Residual
import PV_RJ4IDB_OpenInputs
import R1Z.ProverRwFullFuns
/-! adopted by owner decision D502/D478. A conditional event-retaining headline.
The historical Result-only endpoint and the simulator are unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace PV_MEAS_Legacy
open R1Z
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

abbrev input : HonestProver K := PV_EVH_Core.input

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


open PV_RJ4IDB PV_EVH_Interface PV_EVH_Core
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
variable {Public Signal Env A R S N : Type} [Fintype R] [Nonempty R]
  [Fintype S] [Nonempty S] [Fintype Env] [Nonempty Env]
  [Fintype N] [Nonempty N]


open MeasureTheory PV_MEAS_Law PV_MEAS_Uniform PV_MEAS_Finite
local instance nativeSpace : MeasurableSpace R := ⊤
local instance commonSpace : MeasurableSpace S := ⊤
local instance environmentSpace : MeasurableSpace Env := ⊤
local instance acquisitionSpace : MeasurableSpace N := ⊤
local instance signalSpace : MeasurableSpace Signal := ⊤
local instance observationSpace : MeasurableSpace (Signal × Observation A) := ⊤
local instance realModelSpace : MeasurableSpace (source).RealRand := ⊤
local instance idealModelSpace : MeasurableSpace (source).IdealRand := ⊤
local instance answerSpace : MeasurableSpace OracleAnswer := ⊤
local instance tapeSpace : MeasurableSpace ProverCommitFuelJoin22.Tape := ⊤

variable (rt : PrivacyR1HeadlineDeployedEvents.Runtime (Public := Public) (Signal := Signal)
  (Env := Env) (A := A) (R := R) (S := S) (N := N) template outputs x)

def ofLegacy : PV_MEAS_Deployed.Runtime (Public := Public) (Signal := Signal)
  (Env := Env) (A := A) (R := R) (S := S) (N := N) template outputs x where
  environmentLaw := uniform Env
  nativeLaw := fun _ => uniform R
  acquisitionLaw := uniform N
  jointLaw := uniform (Env × R)
  commonLaw := fun _ _ _ => uniform S
  completion := rt.completion
  publicInput := rt.publicInput
  acquisition := rt.acquisition
  native := rt.native
  signal := rt.signal
  toNative := rt.toNative
  toModel := rt.toModel
  published := rt.published
  compact := rt.compact
  statementBytes := rt.statementBytes
  fileTrace := rt.fileTrace
  jsonStdout := rt.jsonStdout
  errorStderr := rt.errorStderr
  countTrace := rt.countTrace
  timeTrace := rt.timeTrace
  oraclePrefix := rt.oraclePrefix
  retained := rt.retained
  actualProgram := rt.actualProgram
  ops := rt.ops
  terminal := rt.terminal
  semantic := rt.semantic
  point := rt.point

/-- Every old finite conjunction supplies the measured conjunction. No new
native obligation is required in this finite specialization. -/
theorem links_of_legacy (links : PrivacyR1HeadlineDeployedEvents.Links template outputs x rt) :
    PV_MEAS_Deployed.Links template outputs x (ofLegacy template outputs x rt) where
  RUNJOIN_PUBLISH_COMPACT := links.RUNJOIN_PUBLISH_COMPACT
  RUNJOIN_STATEMENT_BYTES := links.RUNJOIN_STATEMENT_BYTES
  DIAG_FILE_TRACE := links.DIAG_FILE_TRACE
  DIAG_JSON_STDOUT_TRACE := links.DIAG_JSON_STDOUT_TRACE
  DIAG_ERROR_STDERR_TRACE := links.DIAG_ERROR_STDERR_TRACE
  L1_COUNT_TRACE := links.L1_COUNT_TRACE
  L1_TIME_TRACE := links.L1_TIME_TRACE
  L1_ORACLE_PREFIX := links.L1_ORACLE_PREFIX
  L1_RETAINED_SIDECHANNELS := links.L1_RETAINED_SIDECHANNELS
  coupling := by
    intro e adv w
    dsimp only [ofLegacy]
    refine ⟨measurable_of_finite _,measurable_of_finite _,?_,?_⟩
    · simpa only [Measure.map_id] using map_uniform_of_means
        (rt.toNative e adv w) (id : R → R) (measurable_of_finite _) measurable_id
        (links.coupling e adv w).1
    · simpa only [Measure.map_id, PV_MEAS_Deployed.input, PV_EVH_Core.input,
        PrivacyR1HeadlineDeployedEvents.input, PV_MEAS_Deployed.ownedDecode, ownedDecode] using map_uniform_of_means
        (Z := (((source).RealRand × OracleAnswer) × ProverCommitFuelJoin22.Tape))
        (rt.toModel e adv w) (id : (((source).RealRand × OracleAnswer) × ProverCommitFuelJoin22.Tape) → _)
        (measurable_of_finite _) measurable_id (links.coupling e adv w).2
  context := links.context
  timing := links.timing
  signal := links.signal
  publicSignal := by
    intro adv w hw
    refine ⟨measurable_of_finite _,measurable_of_finite _,?_⟩
    apply map_uniform_of_means _ _ (measurable_of_finite _) (measurable_of_finite _)
    intro test
    have hl := R0Z.LawTransport.mean_eq_of_equalLaws
      (fun n => rt.signal (rt.acquisition n).1 adv w (rt.acquisition n).2)
      (fun p : Env × R => rt.completion.signal rt.publicInput p.1) test
      (links.publicSignal adv w hw)
    exact hl.trans (CouplingR1PBin.mp_fst (fun e => test (rt.completion.signal rt.publicInput e)))
  environment := by
    refine ⟨measurable_of_finite _,?_⟩
    dsimp only [ofLegacy]
    simpa only [Measure.map_id] using
      map_uniform_of_means rt.acquisition id (measurable_of_finite _) measurable_id
        (fun test => R0Z.LawTransport.mean_eq_of_equalLaws _ _ test links.environment)
  conditional := by
    intro f hf hb
    exact integral_uniform_product f (fun p => (hb p).1)
  decisions := by
    intro adv ha
    exact ⟨fun _ => measurable_of_finite _,fun _ _ => measurable_of_finite _,
      fun _ => measurable_of_finite _,measurable_of_finite _⟩
  causal := links.causal
  observer := links.observer
  selectedCallback := links.selectedCallback

/-- The full former finite deployed event inequality follows from the measured
headline and exact integral/mean conversion. This proof never calls the former
privacy_headline_deployed_events theorem. -/
theorem finite_uniform_corollary (links : PrivacyR1HeadlineDeployedEvents.Links template outputs x rt) :
    (∀ (adv : Observer Signal A) (w : (h).Instance), (h).public w = x.1 →
      |mean (fun r => bit (adv.decide (PrivacyR1HeadlineDeployedEvents.deployedReal template outputs x rt adv w r))) -
        mean (fun r => bit (adv.decide (PrivacyR1HeadlineDeployedEvents.deployedIdeal template outputs x rt adv r)))| ≤
        PV_EVH_Core.bound template outputs x) ∧
    PV_EVH_Core.bound template outputs x ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 +
        QueryScanFreshUnion.freshBudget (8 * n1 W Pr + 1) +
        2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    PV_EVH_Core.bound template outputs x < 1 / 2^100 := by
  constructor
  · intro adv w hw
    have measured := (PV_MEAS_Deployed.privacy_headline_deployed_events_meas template outputs x
      (ofLegacy template outputs x rt) (links_of_legacy template outputs x rt links)).1
      adv (by intro s hs; trivial) w hw
    change |(∫ₚ n, (bit (adv.decide (PrivacyR1HeadlineDeployedEvents.deployedReal template outputs x rt adv w n)) : ℝ)
        ∂(uniform N : Measure N)) -
      (∫ₚ e, (∫ₚ r, (bit (adv.decide (PV_EVH_Core.ideal template outputs x rt.completion rt.publicInput e adv r)) : ℝ)
        ∂(uniform (source).IdealRand : Measure (source).IdealRand)) ∂(uniform Env : Measure Env))| ≤
        (PV_EVH_Core.bound template outputs x : ℝ) at measured
    have product := integral_uniform_product
      (fun p : Env × (source).IdealRand =>
        (bit (adv.decide (PV_EVH_Core.ideal template outputs x rt.completion rt.publicInput p.1 adv p.2)) : ℝ))
      (fun p => by exact_mod_cast (bit_nonneg
        (adv.decide (PV_EVH_Core.ideal template outputs x rt.completion rt.publicInput p.1 adv p.2))))
    rw [← product, integral_bit_mean, integral_bit_mean] at measured
    have casted :
        ((|mean (fun n => bit (adv.decide
          (PrivacyR1HeadlineDeployedEvents.deployedReal template outputs x rt adv w n))) -
          mean (fun p => bit (adv.decide
          (PrivacyR1HeadlineDeployedEvents.deployedIdeal template outputs x rt adv p)))| : ℚ) : ℝ) ≤
          (PV_EVH_Core.bound template outputs x : ℝ) := by
      simpa only [Rat.cast_abs, Rat.cast_sub,
        PrivacyR1HeadlineDeployedEvents.deployedIdeal, PV_EVH_Average.idealExperiment] using measured
    exact Rat.cast_le.mp casted
  · let e : Env := Classical.choice (inferInstance : Nonempty Env)
    exact (PV_MEAS_Core.privacy_headline_events_model template outputs x
      (uniform R) rt.completion rt.publicInput e rt.native rt.signal
      (fun adv w _ => PV_MEAS_Deployed.toCoreLinks template outputs x
        (ofLegacy template outputs x rt) (links_of_legacy template outputs x rt links) e adv w)).2

#print axioms links_of_legacy
#print axioms finite_uniform_corollary
end PV_MEAS_Legacy
