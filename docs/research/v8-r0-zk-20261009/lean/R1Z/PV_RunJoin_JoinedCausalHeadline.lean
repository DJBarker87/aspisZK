import R1Z.PV_RunJoin_JoinedFamily
import R1Z.PV_RunJoin_CausalTrustLedger
import R1Z.PV_RunJoin_SourceSelectionContract
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace R1Z.PV_RunJoin_JoinedCausalHeadline
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
variable (baseTypes : ProverRwFull.ExternalTypes)
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {N Client Context Rest : Type} [Fintype Rest]
variable (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (address : PV_RunJoin_LedgerWorld.Address)
variable (coordinates : ModelCoins template outputs x ≃ PV_RunJoin_CausalPrefix.Tape × Rest)
    (replies : ModelCoins template outputs x → Fin 128 →
      (Aeneas.Std.Array Aeneas.Std.U8 64#usize ×
        Aeneas.Std.core.result.Result Unit ProverRwRngCaller.getrandom.error.Error))
    (initialPolicy : Rest → N) (initialLedger : Rest → (@PV_RunJoin_LedgerWorld.World (PV_Join_PublicCaller.native baseTypes)))
    (initialBody : Rest → Client)
local notation "world" => PV_RunJoin_CausalPrefix.world coordinates replies initialPolicy initialLedger initialBody
variable    (policy : ProverRwEffectCallback.Account N)
    (disclosed : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Aeneas.Std.Result (PV_RunJoin_Deployed.Output N (@PV_RunJoin_LedgerWorld.World (PV_Join_PublicCaller.native baseTypes)) Client) → View K CommitHandle Aux R1Bat)
    (oracle : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Aeneas.Std.Result (PV_RunJoin_Deployed.Output N (@PV_RunJoin_LedgerWorld.World (PV_Join_PublicCaller.native baseTypes)) Client) → List (Bytes × OracleAnswer))
    (ideal : (Challenges K → R0Z.JointView.Tape K F → View K CommitHandle Aux R1Bat) →
      R1Adv K CommitHandle Aux → Statement K CommitHandle → ROMView K CommitHandle Aux R1Bat)
variable (ops : PV_Join_LedgerSource.World baseTypes N Client →
    @ProverRwFull.ExternalFuns (PV_Join_PublicCaller.native baseTypes))
    (hash : Statement K CommitHandle → Aeneas.Std.Slice (Aeneas.Std.Slice Aeneas.Std.U8) →
      Aeneas.Std.Result (Aeneas.Std.Array Aeneas.Std.U8 32#usize))
    (selected : PV_RunJoin_InstalledFamily.Selection CommitHandle)
local notation "runtime" => (@PV_RunJoin_LedgerConstructor.runtime (PV_Join_PublicCaller.native baseTypes)) schedule unix address world policy (PV_RunJoin_JoinedFamily.inputs baseTypes ops hash selected) disclosed oracle ideal
variable (boundaryData : @PV_RunJoin_Boundary.Data (PV_Join_PublicCaller.native baseTypes) _ _ _ _ _ _
  ((@PV_RunJoin_LedgerConstructor.runtime (PV_Join_PublicCaller.native baseTypes)) schedule unix address
    (PV_RunJoin_CausalPrefix.world coordinates replies initialPolicy initialLedger initialBody)
    policy (PV_RunJoin_JoinedFamily.inputs baseTypes ops hash selected) disclosed oracle ideal) Context Rest)
variable (produce : (i : Fin 128) → PV_RunJoin_CausalPrefix.Prefix i → Rest → Context)
local notation "causalData" => (letI : ProverRwFull.ExternalTypes := PV_Join_PublicCaller.native baseTypes; { boundaryData with
  frame := PV_RunJoin_CausalPrefix.frame produce
  coordinates := coordinates })

local notation "boundary" => (@PV_RunJoin_LedgerBoundary.boundary (PV_Join_PublicCaller.native baseTypes)) schedule unix address world policy (PV_RunJoin_JoinedFamily.inputs baseTypes ops hash selected) (PV_RunJoin_JoinedFamily.common baseTypes ops hash selected) disclosed oracle ideal x causalData
local notation "rust" => PV_RunJoin_Deployed.rust runtime
local notation "observer_program" => PV_RunJoin_Deployed.observer_program runtime
local notation "World" => PV_RunJoin_Deployed.World runtime
local notation "State" => PV_RunJoin_Deployed.State N (@PV_RunJoin_LedgerWorld.World (PV_Join_PublicCaller.native baseTypes)) Client
local notation "oldBad" => QueryScanRealLazyBound.realBad W Pr 8 h B outputs x
local notation "queries" => PrivacyR1HeadlineDeployedReal.realSeedQueries template outputs x rust observer_program

variable (extracted : ModelCoins template outputs x → R1Adv K CommitHandle Aux →
  (h).Instance → ROMView K CommitHandle Aux R1Bat)

/-- The published joined proof-account dictionary, initial constructor, and public binding supply these
candidate laws directly. Neither is a premise of this constructor. Selection and its fixed-endpoint public binding remain explicit; no actual compiler or native
observer installation is inferred. -/
theorem proofs
    (binding : ∀ (w : (h).Instance), (h).public w = x.1 →
      PV_Src_NativeInput.publicInput (selected.selected h x w) =
        PV_Src_NativeInput.publicInput (selected.publicRecord x))
    (trace : ∀ (adv : R1Adv K CommitHandle Aux) (w : (h).Instance), (h).public w = x.1 →
      ∀ r : World, ¬ (∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins) →
        extracted r.coins adv w =
          (source).real h B outputs (RomObserverBin.observerMap rust observer_program adv) x w r.coins.1.1) :
    (@PV_RunJoin_TrustEndpoint.ProofObligations _ _ template outputs x (PV_Join_PublicCaller.native baseTypes)) runtime boundary extracted := by
  apply (@PV_RunJoin_TrustLedger.candidate_proofs _ _ template outputs x (PV_Join_PublicCaller.native baseTypes)) schedule unix address
    world policy (PV_RunJoin_JoinedFamily.inputs baseTypes ops hash selected) disclosed oracle ideal (PV_RunJoin_JoinedFamily.common baseTypes ops hash selected) causalData extracted
  · intro hh xx ww ss
    exact PV_RunJoin_JoinedFamily.identity baseTypes ops hash selected hh xx ww ss
  · intro w hw s
    exact PV_RunJoin_JoinedInstallation.common_public baseTypes ops (hash x)
      (selected.selected h x w) (selected.publicRecord x) (binding w hw) s
  · exact (@PV_RunJoin_CausalTrustLedger.initial_and_causal _ _ template outputs x (PV_Join_PublicCaller.native baseTypes))
      (schedule := schedule) (unix := unix) (address := address)
      (coordinates := coordinates) (replies := replies) (initialPolicy := initialPolicy)
      (initialLedger := initialLedger) (initialBody := initialBody) (policy := policy)
      (disclosed := disclosed) (oracle := oracle) (ideal := ideal) (inputs := (PV_RunJoin_JoinedFamily.inputs baseTypes ops hash selected)) (common := (PV_RunJoin_JoinedFamily.common baseTypes ops hash selected))
      (boundaryData := boundaryData) (produce := produce) (extracted := extracted) trace

variable {E File Reply Time Worker : Type} [DecidableEq File]
variable (nativeEvents extractedEvents : ModelCoins template outputs x →
  PV_RunJoin_TrustBoundary.Observation E File Reply Time Worker Unit)

/-- Exact headline at the candidate ledger construction. Source selection/public binding and extracted complete trace refinement remain
P work. Initial-ledger independence and prefix causality are derived. No actual native runtime/boundary installation is claimed. -/
theorem privacy_headline_deployed_candidate
    (binding : ∀ (w : (h).Instance), (h).public w = x.1 →
      PV_Src_NativeInput.publicInput (selected.selected h x w) =
        PV_Src_NativeInput.publicInput (selected.publicRecord x))
    (trace : ∀ (adv : R1Adv K CommitHandle Aux) (w : (h).Instance), (h).public w = x.1 →
      ∀ r : World, ¬ (∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins) →
        extracted r.coins adv w =
          (source).real h B outputs (RomObserverBin.observerMap rust observer_program adv) x w r.coins.1.1)
    (T : PV_RunJoin_TrustItems
      ((@PV_RunJoin_TrustEndpoint.trustData _ _ template outputs x (PV_Join_PublicCaller.native baseTypes)) runtime boundary nativeEvents extractedEvents extracted))
 :
    (∀ (adv : R1Adv K CommitHandle Aux) (w : (h).Instance), (h).public w = x.1 →
      |mean (realTest h B outputs rust adv x w) -
        mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
          (simE (h).transport B outputs x))| ≤
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100 := by
  exact (@PV_RunJoin_TrustEndpoint.privacy_headline_deployed_candidate _ _ template outputs x (PV_Join_PublicCaller.native baseTypes)) runtime boundary nativeEvents extractedEvents extracted
    (proofs (template := template) (outputs := outputs) (x := x) (baseTypes := baseTypes)
      (schedule := schedule) (unix := unix) (address := address) (coordinates := coordinates)
      (replies := replies) (initialPolicy := initialPolicy) (initialLedger := initialLedger)
      (initialBody := initialBody) (policy := policy) (disclosed := disclosed) (oracle := oracle) (ideal := ideal)
      (ops := ops) (hash := hash) (selected := selected) (boundaryData := boundaryData)
      (produce := produce) (extracted := extracted) binding trace) T

#print axioms proofs
#print axioms privacy_headline_deployed_candidate
end R1Z.PV_RunJoin_JoinedCausalHeadline
