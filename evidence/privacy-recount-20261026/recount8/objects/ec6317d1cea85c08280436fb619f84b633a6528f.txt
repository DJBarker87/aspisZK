import R1Z.PV_RunJoin_Endpoint
import R1Z.PV_RunJoin_OsFailure
import R1Z.PV_RunJoin_ErrorViewObstruction
import R1Z.PV_RunJoin_AbstractEndpoint
import R1Z.PV_RunJoin_WorldCoupling
import R1Z.PV_RunJoin_Boundary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FailurePremiseObstruction
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

abbrev ModelCoins := (((source).RealRand × OracleAnswer) × ProverCommitFuelJoin22.Tape)
variable [ProverRwFull.ExternalTypes]
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {N Ledger Client Context Rest : Type} [Fintype Rest]
variable (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux (ModelCoins template outputs x) N Ledger Client)
variable (boundary : PV_RunJoin_Boundary.Data runtime Context Rest)
local notation "rust" => PV_RunJoin_Deployed.rust runtime
local notation "observer_program" => PV_RunJoin_Deployed.observer_program runtime
local notation "World" => PV_RunJoin_Deployed.World runtime
local notation "State" => PV_RunJoin_Deployed.State N Ledger Client
local notation "oldBad" => QueryScanRealLazyBound.realBad W Pr 8 h B outputs x
local notation "queries" => PrivacyR1HeadlineDeployedReal.realSeedQueries template outputs x rust observer_program

/-- If the exact safe failure/source-success disagreement is installed at
one deployed world, the current endpoint premises cannot be inhabited.
This pinpoints the original V038 observerOracle obligation; it is not a
counterexample to witness privacy with an approved public-failure model. -/
theorem no_premises_on_safe_log_disagreement
    (adv : (rust).Adversary) (w : (h).Instance) (hw : (h).public w = x.1)
    (r : World)
    (safe : ¬ ∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins)
    (disagreement : ((rust).real h B outputs adv x w r).observerOracle ≠
      ((source).real h B outputs (RomObserverBin.observerMap rust observer_program adv) x w r.coins.1.1).observerOracle) :
    ¬ PV_RunJoin_Endpoint.PV_RunJoin_Premises template outputs x runtime boundary := by
  intro premises
  exact disagreement (premises.observerOracle_V038 adv w hw r safe)

#print axioms no_premises_on_safe_log_disagreement
end R1Z.PV_RunJoin_FailurePremiseObstruction
