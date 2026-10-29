import PV_EVH_Deployed
import R1Z.PV_RunJoin_NativePublication55
import R1Z.PV_RunJoin_ActualRun59
/-! adopted by owner decision D502/D478. A conditional event-retaining headline.
The historical Result-only endpoint and the simulator are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVH_RuntimeBinding
open R1Z.PrivacyR1HeadlineDeployedEvents
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


open PV_RJ4IDB PV_EVH_Interface PV_EVH_Core
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
variable {Public Signal Env A R S N : Type} [Fintype R] [Nonempty R]
  [Fintype S] [Nonempty S] [Fintype Env] [Nonempty Env]
  [Fintype N] [Nonempty N]


/-- Missing selections are DATA obligations, not trust or proof instances.
No value of this structure is supplied. In particular native_OPEN must retain
all events, not reconstruct them from a Result. -/
structure OpenDeploymentInputs (T : Type) where
  completion_OPEN : Completion Public Signal Env (ROMView K CommitHandle Aux R1Bat) A
  publicInput_OPEN : Public
  acquisition_OPEN : N → Env × R
  native_OPEN : Env → Observer Signal A → (h).Instance → R → NativeTrace A
  signal_OPEN : Env → Observer Signal A → (h).Instance → R → Signal
  toNative_OPEN : Env → Observer Signal A → (h).Instance → S → R
  toModel_OPEN : Env → Observer Signal A → (h).Instance → S →
    (((source).RealRand × OracleAnswer) × ProverCommitFuelJoin22.Tape)
  statementBytes_OPEN : Env × Observer Signal A × (h).Instance × R → Option PV_RJ4IDB.Bytes
  fileTrace_OPEN : Env × Observer Signal A × (h).Instance × R → List FileOp
  jsonStdout_OPEN : Env × Observer Signal A × (h).Instance × R →
    List PV_RJ4IDB.Bytes × List (PV_RJ4IDB.Bytes × PV_RJ4IDB.Bytes)
  errorStderr_OPEN : Env × Observer Signal A × (h).Instance × R →
    List PV_DIAG2.Effect × List PV_DIAG3.Event
  countTrace_OPEN : Env × Observer Signal A × (h).Instance × R → List Nat × List Nat
  timeTrace_OPEN : Env × Observer Signal A × (h).Instance × R → List PV_RJ4IDB.Bytes
  oraclePrefix_OPEN : Env × Observer Signal A × (h).Instance × R →
    List (PV_RJ4IDB.Bytes × PV_RJ4IDB.Bytes)
  retained_OPEN : Env × Observer Signal A × (h).Instance × R →
    List (PV_RJ4IDB.Bytes × PV_RJ4IDB.Bytes)
  actualProgram_OPEN : Observer Signal A → Env × View K CommitHandle Aux R1Bat ×
    List (R0Z.FsStatement.Bytes × OracleAnswer) → OProg
  terminal_OPEN : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
    Array (Array aspis_core.field.QM31 29#usize) 3#usize →
    Array aspis_core.field.QM31 10#usize →
    aspis_core.state_only_prefix.r0.Challenges →
    Result (core.result.Result aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error)
  semantic_OPEN : Env × Observer Signal A × (h).Instance × R → host_semantic.SemanticOracle
  point_OPEN : Env × Observer Signal A × (h).Instance × R → Array aspis_core.field.QM31 10#usize
  invocation_OPEN : Env × Observer Signal A × (h).Instance × R →
    PV_RunJoin_NativePublication55.Input T

variable [ExternalFuns] {T : Type}
variable (missing : OpenDeploymentInputs (Public := Public) (Signal := Signal)
  (Env := Env) (A := A) (R := R) (S := S) (N := N) template outputs x T)
variable (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T)

/-- Partially selected deployed binding. Only publication and compact are
bound to existing source definitions. Every other missing selection remains
named in OpenDeploymentInputs; this is NOT a supplied live runtime. -/
def rtDeployed : Runtime (Public := Public) (Signal := Signal) (Env := Env)
    (A := A) (R := R) (S := S) (N := N) template outputs x where
  completion := missing.completion_OPEN
  publicInput := missing.publicInput_OPEN
  acquisition := missing.acquisition_OPEN
  native := missing.native_OPEN
  signal := missing.signal_OPEN
  toNative := missing.toNative_OPEN
  toModel := missing.toModel_OPEN
  statementBytes := missing.statementBytes_OPEN
  fileTrace := missing.fileTrace_OPEN
  jsonStdout := missing.jsonStdout_OPEN
  errorStderr := missing.errorStderr_OPEN
  countTrace := missing.countTrace_OPEN
  timeTrace := missing.timeTrace_OPEN
  oraclePrefix := missing.oraclePrefix_OPEN
  retained := missing.retained_OPEN
  actualProgram := missing.actualProgram_OPEN
  ops := inferInstance
  terminal := missing.terminal_OPEN
  semantic := missing.semantic_OPEN
  point := missing.point_OPEN
  compact := fun i => PV_RunJoin_NativePublication55.actual store (missing.invocation_OPEN i)
  published := fun i => PV_RunJoin_NativePublication55.published
    PV_RunJoin_ActualRun.data PV_RunJoin_ActualRun.plans store (missing.invocation_OPEN i)

/-- Separate live-domain obligation. Neither finite nonempty sample carriers
nor consistency of phase-restricted links supplies this witness. -/
def LivePublication : Prop :=
  ∃ (i : Env × Observer Signal A × (h).Instance × R)
    (bytes : PV_RJ4IDB.Bytes) (publication : PublicationInput),
    (rtDeployed template outputs x missing store).compact i = some bytes ∧
    (rtDeployed template outputs x missing store).published i = some publication

/-- Authoritative specialised obligations, still without a joint witness. -/
abbrev DeployedLinks := Links template outputs x (rtDeployed template outputs x missing store)

theorem privacy_headline_deployed_events_at (links : DeployedLinks template outputs x missing store) :
    (∀ (adv : Observer Signal A) (w : (h).Instance), (h).public w = x.1 →
      |mean (fun r => bit (adv.decide (deployedReal template outputs x (rtDeployed template outputs x missing store) adv w r))) -
        mean (fun r => bit (adv.decide (deployedIdeal template outputs x (rtDeployed template outputs x missing store) adv r)))| ≤
        PV_EVH_Core.bound template outputs x) ∧
    PV_EVH_Core.bound template outputs x ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 +
        QueryScanFreshUnion.freshBudget (8 * n1 W Pr + 1) +
        2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    PV_EVH_Core.bound template outputs x < 1 / 2^100 := by
  exact privacy_headline_deployed_events template outputs x
    (rtDeployed template outputs x missing store) links

#print axioms rtDeployed
#print axioms LivePublication
#print axioms privacy_headline_deployed_events_at
end PV_EVH_RuntimeBinding
