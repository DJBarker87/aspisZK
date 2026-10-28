import R1Z.PV_RunJoin_TrustLedger
import R1Z.PV_RunJoin_CausalPrefix
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CausalTrustLedger
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
variable {N Client Context Rest : Type} [Fintype Rest]
variable (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (address : PV_RunJoin_LedgerWorld.Address)
variable (coordinates : ModelCoins template outputs x ≃ PV_RunJoin_CausalPrefix.Tape × Rest)
    (replies : ModelCoins template outputs x → Fin 128 →
      (Aeneas.Std.Array Aeneas.Std.U8 64#usize ×
        Aeneas.Std.core.result.Result Unit ProverRwRngCaller.getrandom.error.Error))
    (initialPolicy : Rest → N)
    (initialLedger : Rest → PV_RunJoin_LedgerWorld.World)
    (initialBody : Rest → Client)
local notation "world" => PV_RunJoin_CausalPrefix.world coordinates replies initialPolicy initialLedger initialBody
variable    (policy : ProverRwEffectCallback.Account N)
    (disclosed : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Aeneas.Std.Result (PV_RunJoin_Deployed.Output N PV_RunJoin_LedgerWorld.World Client) → View K CommitHandle Aux R1Bat)
    (oracle : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Aeneas.Std.Result (PV_RunJoin_Deployed.Output N PV_RunJoin_LedgerWorld.World Client) → List (Bytes × OracleAnswer))
    (ideal : (Challenges K → R0Z.JointView.Tape K F → View K CommitHandle Aux R1Bat) →
      R1Adv K CommitHandle Aux → Statement K CommitHandle → ROMView K CommitHandle Aux R1Bat)
variable (inputs : (honest : HonestProver K) → (statement : Statement K CommitHandle) → honest.Instance →
      PV_RunJoin_LedgerBody.Inputs N Client)
    (common : Statement K CommitHandle → PV_RunJoin_LedgerBody.Inputs N Client)
local notation "runtime" => PV_RunJoin_LedgerConstructor.runtime schedule unix address world policy inputs disclosed oracle ideal
variable (boundaryData : PV_RunJoin_Boundary.Data
  (PV_RunJoin_LedgerConstructor.runtime schedule unix address
    (PV_RunJoin_CausalPrefix.world coordinates replies initialPolicy initialLedger initialBody)
    policy inputs disclosed oracle ideal) Context Rest)
variable (produce : (i : Fin 128) → PV_RunJoin_CausalPrefix.Prefix i → Rest → Context)
local notation "causalData" => (PV_RunJoin_Boundary.Data.mk
  boundaryData.sourceBody boundaryData.draw boundaryData.law
  (PV_RunJoin_CausalPrefix.frame produce) coordinates boundaryData.nativeWeight
  boundaryData.ledger boundaryData.reservation boundaryData.schedule boundaryData.unix boundaryData.fault :
    PV_RunJoin_Boundary.Data runtime Context Rest)
local notation "boundary" => PV_RunJoin_LedgerBoundary.boundary schedule unix address world policy inputs common disclosed oracle ideal x causalData
local notation "rust" => PV_RunJoin_Deployed.rust runtime
local notation "observer_program" => PV_RunJoin_Deployed.observer_program runtime
local notation "World" => PV_RunJoin_Deployed.World runtime
local notation "State" => PV_RunJoin_Deployed.State N PV_RunJoin_LedgerWorld.World Client
local notation "oldBad" => QueryScanRealLazyBound.realBad W Pr 8 h B outputs x
local notation "queries" => PrivacyR1HeadlineDeployedReal.realSeedQueries template outputs x rust observer_program

variable (extracted : ModelCoins template outputs x → R1Adv K CommitHandle Aux →
  (h).Instance → ROMView K CommitHandle Aux R1Bat)

/-- Initial ledger independence and prior causality are proved for the
specified constructed data. Trace remains the exact original obligation. No
claim that a deployed native initializer equals these data is implicit. -/
theorem initial_and_causal
    (trace : ∀ (adv : R1Adv K CommitHandle Aux) (w : (h).Instance), (h).public w = x.1 →
      ∀ r : World, ¬ (∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins) →
        extracted r.coins adv w =
          (source).real h B outputs (RomObserverBin.observerMap rust observer_program adv) x w r.coins.1.1) :
    PV_RunJoin_TrustLedger.RemainingProofs template outputs x schedule unix address
      world policy inputs disclosed oracle ideal common causalData extracted := by
  refine { initial := ?_, causal := PV_RunJoin_CausalPrefix.causal produce, trace := trace }
  ·
    intro t u rest
    change ((PV_RunJoin_CausalPrefix.world coordinates replies initialPolicy initialLedger initialBody).ledger
      (coordinates.symm (t,rest))).model =
        ((PV_RunJoin_CausalPrefix.world coordinates replies initialPolicy initialLedger initialBody).ledger
          (coordinates.symm (u,rest))).model
    exact congrArg PV_RunJoin_LedgerWorld.World.model
      (PV_RunJoin_CausalPrefix.initial_ledger coordinates replies initialPolicy initialLedger initialBody t u rest)

#print axioms initial_and_causal
end R1Z.PV_RunJoin_CausalTrustLedger
