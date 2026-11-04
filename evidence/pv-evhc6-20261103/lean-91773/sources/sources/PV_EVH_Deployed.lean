import R1Z.ProverCommitDeployedFuel22
import PV_EVH_Average
import PV_EVH_Residual
import PV_RJ4IDB_OpenInputs
import R1Z.ProverRwFullFuns
/-! adopted by owner decision D502/D478. A conditional event-retaining headline.
The historical Result-only endpoint and the simulator are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineDeployedEvents
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

/-- adopted by owner decision D502/D478. Data for the exact deployed invocation.
No proof fields, Result decoder, success restriction or extra trust field.
Native acquisition is indexed by every observer, witness, coin and prefix policy;
the public invocation includes the stopping policy, never the witness or elapsed time. -/
structure Runtime where
  completion : Completion Public Signal Env (ROMView K CommitHandle Aux R1Bat) A
  publicInput : Public
  acquisition : N → Env × R
  native : Env → Observer Signal A → (h).Instance → R → NativeTrace A
  signal : Env → Observer Signal A → (h).Instance → R → Signal
  toNative : Env → Observer Signal A → (h).Instance → S → R
  toModel : Env → Observer Signal A → (h).Instance → S →
    (((source).RealRand × OracleAnswer) × ProverCommitFuelJoin22.Tape)
  published : Env × Observer Signal A × (h).Instance × R → Option PublicationInput
  compact : Env × Observer Signal A × (h).Instance × R → Option PV_RJ4IDB.Bytes
  statementBytes : Env × Observer Signal A × (h).Instance × R → Option PV_RJ4IDB.Bytes
  fileTrace : Env × Observer Signal A × (h).Instance × R → List FileOp
  jsonStdout : Env × Observer Signal A × (h).Instance × R →
    List PV_RJ4IDB.Bytes × List (PV_RJ4IDB.Bytes × PV_RJ4IDB.Bytes)
  errorStderr : Env × Observer Signal A × (h).Instance × R →
    List PV_DIAG2.Effect × List PV_DIAG3.Event
  countTrace : Env × Observer Signal A × (h).Instance × R → List Nat × List Nat
  timeTrace : Env × Observer Signal A × (h).Instance × R → List PV_RJ4IDB.Bytes
  oraclePrefix : Env × Observer Signal A × (h).Instance × R →
    List (PV_RJ4IDB.Bytes × PV_RJ4IDB.Bytes)
  retained : Env × Observer Signal A × (h).Instance × R →
    List (PV_RJ4IDB.Bytes × PV_RJ4IDB.Bytes)
  actualProgram : Observer Signal A → Env × View K CommitHandle Aux R1Bat ×
    List (R0Z.FsStatement.Bytes × OracleAnswer) → OProg
  ops : ExternalFuns
  terminal : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public →
    Array (Array aspis_core.field.QM31 29#usize) 3#usize →
    Array aspis_core.field.QM31 10#usize →
    aspis_core.state_only_prefix.r0.Challenges →
    Result (core.result.Result aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error)
  semantic : Env × Observer Signal A × (h).Instance × R → host_semantic.SemanticOracle
  point : Env × Observer Signal A × (h).Instance × R → Array aspis_core.field.QM31 10#usize

variable (rt : Runtime (Public := Public) (Signal := Signal) (Env := Env)
  (A := A) (R := R) (S := S) (N := N) template outputs x)

def acquired (i : Env × Observer Signal A × (h).Instance × R) : NativeTrace A :=
  rt.native i.1 i.2.1 i.2.2.1 i.2.2.2

/-- adopted by owner decision D502/D478. D163 with both exact marginals on
one common carrier. The native coordinate is the same acquisition used by all nine inputs. -/
def D163 : Prop :=
  ∀ e adv w,
    (∀ f : R → ℚ, mean (fun s => f (rt.toNative e adv w s)) = mean f) ∧
    (∀ f : (((source).RealRand × OracleAnswer) × ProverCommitFuelJoin22.Tape) → ℚ,
      mean (fun s => f (rt.toModel e adv w s)) = mean f)

def bad (e : Env) (adv : Observer Signal A) (w : (h).Instance) (s : S) : Prop :=
  ∃ i, ProverCommitFuelJoin22.bad
    (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
    (PV_EVH_Core.seedQueries template outputs x rt.completion rt.publicInput e adv w)
    i (rt.toModel e adv w s)

def surrogate (e : Env) (adv : Observer Signal A) (w : (h).Instance) (s : S) : NativeTrace A :=
  rt.completion.complete rt.publicInput (rt.completion.signal rt.publicInput e) e
    ((source).real h B outputs
      (observer rt.completion rt.publicInput e adv) x w (rt.toModel e adv w s).1.1)

/-- adopted by owner decision D502/D478. Ordered-event context is a pathwise
law on the original good sample, including terminal tags and failed/divergent prefixes. -/
def OrderedEventContext : Prop := ∀ e adv w,
  Link_Context (bad template outputs x rt e adv w)
    (fun s => rt.native e adv w (rt.toNative e adv w s))
    (surrogate template outputs x rt e adv w)

/-- adopted by owner decision D502/D478. D166 is joint timing on that same
sample; serialized clock copies remain in OrderedEventContext. -/
def D166 : Prop := ∀ e adv w,
  Link_Timing (bad template outputs x rt e adv w)
    (fun s => rt.native e adv w (rt.toNative e adv w s))
    (surrogate template outputs x rt e adv w)

def SignalAgreement : Prop := ∀ e adv w,
  Link_Signal (bad template outputs x rt e adv w)
    (fun s => rt.signal e adv w (rt.toNative e adv w s))
    (fun _ => rt.completion.signal rt.publicInput e)

/-- adopted by owner decision D502/D478. Existing V400 option-B input,
quantified over all equal-public witnesses; the earlier event prefix is retained. -/
def V400 : Prop := ∀ adv,
  PV_EVH_Residual.Link_PublicSignal (h).public x.1
    (fun w n => rt.signal (rt.acquisition n).1 adv w (rt.acquisition n).2)
    (fun p : Env × R => rt.completion.signal rt.publicInput p.1)

/-- adopted by owner decision D502/D478. Exact JOINT native environment/coin
acquisition law. Neither an identity nor separate timing/signal marginals. -/
def PublicEnvironment : Prop :=
  PV_EVH_Residual.Link_PublicEnvironment rt.acquisition

def CausalPrefix : Prop := PV_EVH_Residual.Link_CausalPrefix
  (fun e v oracleLog => rt.completion.complete rt.publicInput
    (rt.completion.signal rt.publicInput e) e ⟨v,oracleLog⟩)

def ObserverProgram : Prop := ∀ adv, PV_EVH_Residual.Link_ObserverProgram
  (rt.actualProgram adv)
  (fun i => completed rt.completion rt.publicInput i.1 ⟨i.2.1,i.2.2⟩) adv.program

/-- adopted by owner decision D502/D478. V244's existing selected_callback
binder, for every actual caller and every claims array. It remains in progress. -/
def op227 : Prop := ∀ i claims,
  rt.ops.op227 (rt.semantic i).«public» claims (rt.point i) (rt.semantic i).challenges =
    rt.terminal (rt.semantic i).«public» claims (rt.point i) (rt.semantic i).challenges

/-- adopted by owner decision D502/D478. Conjunction of standalone links,
using the nine original typed inputs verbatim. Grouping is not discharge. -/
structure Links : Prop where
  RUNJOIN_PUBLISH_COMPACT : OpenInputs.RUNJOIN_PUBLISH_COMPACT rt.compact rt.published
  RUNJOIN_STATEMENT_BYTES : OpenInputs.RUNJOIN_STATEMENT_BYTES rt.statementBytes rt.published
  DIAG_FILE_TRACE : OpenInputs.DIAG_FILE_TRACE rt.fileTrace (acquired template outputs x rt)
  DIAG_JSON_STDOUT_TRACE : OpenInputs.DIAG_JSON_STDOUT_TRACE rt.jsonStdout (acquired template outputs x rt)
  DIAG_ERROR_STDERR_TRACE : OpenInputs.DIAG_ERROR_STDERR_TRACE rt.errorStderr (acquired template outputs x rt)
  L1_COUNT_TRACE : OpenInputs.L1_COUNT_TRACE rt.countTrace (acquired template outputs x rt)
  L1_TIME_TRACE : OpenInputs.L1_TIME_TRACE rt.timeTrace (acquired template outputs x rt)
  L1_ORACLE_PREFIX : OpenInputs.L1_ORACLE_PREFIX rt.oraclePrefix (acquired template outputs x rt)
  L1_RETAINED_SIDECHANNELS : OpenInputs.L1_RETAINED_SIDECHANNELS rt.retained (acquired template outputs x rt)
  coupling : D163 template outputs x rt
  context : OrderedEventContext template outputs x rt
  timing : D166 template outputs x rt
  signal : SignalAgreement template outputs x rt
  publicSignal : V400 template outputs x rt
  environment : PublicEnvironment template outputs x rt
  causal : CausalPrefix template outputs x rt
  observer : ObserverProgram template outputs x rt
  selectedCallback : op227 template outputs x rt

/-- adopted by owner decision D502/D478. Exact D163/D166 construction;
no full-agreement or privacy conclusion is assumed as a link. -/
def toCoreLinks (links : Links template outputs x rt) (e : Env)
    (adv : Observer Signal A) (w : (h).Instance) :
    PV_EVH_Core.Links template outputs x rt.completion rt.publicInput e rt.native rt.signal adv w where
  cp := ⟨S,inferInstance,inferInstance,rt.toNative e adv w,rt.toModel e adv w,
    (links.coupling e adv w).1,(links.coupling e adv w).2⟩
  context := links.context e adv w
  timing := links.timing e adv w
  signal := links.signal e adv w

/-- adopted by owner decision D502/D478. The deployed real experiment receives
the complete lossless native observation; the adversary carrier is explicitly
Observer Signal A, with arbitrary adaptive programs and Boolean decisions. -/
def deployedReal (adv : Observer Signal A) (w : (h).Instance) (n : N) :=
  PV_EVH_Average.realExperiment rt.native rt.signal adv w (rt.acquisition n)

def deployedIdeal := PV_EVH_Average.idealExperiment template outputs x rt.completion rt.publicInput

/-- adopted by owner decision D502/D478. Authoritative exact event-retaining
headline. The historical Result-only privacy_headline_deployed is unchanged.
All native links are ordinary P, and T has exactly its original three fields. -/
theorem privacy_headline_deployed_events (links : Links template outputs x rt) :
    (∀ (adv : Observer Signal A) (w : (h).Instance), (h).public w = x.1 →
      |mean (fun r => bit (adv.decide (deployedReal template outputs x rt adv w r))) -
        mean (fun r => bit (adv.decide (deployedIdeal template outputs x rt adv r)))| ≤
        PV_EVH_Core.bound template outputs x) ∧
    PV_EVH_Core.bound template outputs x ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 +
        QueryScanFreshUnion.freshBudget (8 * n1 W Pr + 1) +
        2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    PV_EVH_Core.bound template outputs x < 1 / 2^100 := by
  constructor
  · intro adv w hw
    have transfer := R0Z.LawTransport.mean_eq_of_equalLaws rt.acquisition
      (fun p : Env × R => p)
      (fun p => bit (adv.decide (PV_EVH_Average.realExperiment rt.native rt.signal adv w p)))
      links.environment
    change |mean (fun n => bit (adv.decide
      (PV_EVH_Average.realExperiment rt.native rt.signal adv w (rt.acquisition n)))) - _| ≤ _
    rw [transfer]
    exact PV_EVH_Average.privacy_headline_events_joint template outputs x
      rt.completion rt.publicInput rt.native rt.signal
      (fun e adv w _ => toCoreLinks template outputs x rt links e adv w) adv w hw
  · exact (PV_EVH_Core.privacy_headline_events_model template outputs x
      rt.completion rt.publicInput (Classical.choice (inferInstance : Nonempty Env))
      rt.native rt.signal
      (fun adv w _ => toCoreLinks template outputs x rt links _ adv w)).2

#print axioms toCoreLinks
#print axioms privacy_headline_deployed_events
end R1Z.PrivacyR1HeadlineDeployedEvents
