import R1Z.PV_RunJoin_AbstractEndpoint
import R1Z.PV_RunJoin_WorldCoupling
import R1Z.PV_RunJoin_Boundary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Endpoint
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

/-- Eight explicit row obligations. This conditional record is NOT an
instantiated native certificate: the body, effect, kernel and complete-view
fields remain to be proved for the frozen runtime data. No uniform_V037 field
is needed on the constructed graph coupling. -/
structure PV_RunJoin_Premises : Prop where
  source_V045 :
    (∀ w : (h).Instance, (h).public w = x.1 →
      PV_RunJoin_UnifiedRetry.BodySourceLaw (boundary.sourceBody h x w) (runtime.body h x w)) ∧
    (∀ (s : State) k nonce next,
      runtime.account.call_mut s k = .ok (nonce,next) → next.provider = s.provider) ∧
    (∀ (w : (h).Instance), (h).public w = x.1 → ∀ secret (s next : State) status,
      runtime.body h x w secret s = .ok (status,next) → next.provider = s.provider)
  E1_V329 : ProverCommitPublicNonce40.E1 boundary.law
  native_fill_V336 : ∀ (p : ProverRwRngCaller.Tape), p.used.val < p.replies.val.length →
    boundary.draw.fill p (Aeneas.Std.Array.repeat 64#usize 0#u8) =
      ProverRwRngCaller.Tape.Insts.Prover_rw_rng_callerDraw64.fill p (Aeneas.Std.Array.repeat 64#usize 0#u8)
  native_ledger_V337 : ∀ (w : (h).Instance), (h).public w = x.1 →
    ∀ secret (s next : State) status, runtime.body h x w secret s = .ok (status,next) →
      boundary.ledger next =
        match boundary.reservation secret s with
        | none => boundary.ledger s
        | some path => (ProverCommitLedger36.reserve boundary.schedule boundary.unix path (boundary.ledger s)).2
  byte_blind_V338 :
    (∀ secret (s : State) kind,
      boundary.fault secret s kind = boundary.schedule (boundary.ledger s).history.length kind (boundary.ledger s).history) ∧
    (∀ t u rest, boundary.ledger (PV_RunJoin_Deployed.initialState runtime (boundary.coordinates.symm (t,rest))) =
      boundary.ledger (PV_RunJoin_Deployed.initialState runtime (boundary.coordinates.symm (u,rest)))) ∧
    (∀ (i : Fin 128) (t u : Fin 128 → ProverCommitPublicNonce40.Raw) (rest : Rest), (∀ j : Fin 128, j.val < i.val → t j = u j) →
      boundary.frame i (t,rest) = boundary.frame i (u,rest))
  kernels_V339 : ∀ c, boundary.nativeWeight c =
    PV_RunJoin_E1Joint.weight 128 boundary.law boundary.frame boundary.coordinates c
  disclosed_V038 : ∀ (adv : (rust).Adversary) (w : (h).Instance), (h).public w = x.1 →
    ∀ r : World, ¬ (∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins) →
      ((rust).real h B outputs adv x w r).disclosed =
        ((source).real h B outputs (RomObserverBin.observerMap rust observer_program adv) x w r.coins.1.1).disclosed
  observerOracle_V038 : ∀ (adv : (rust).Adversary) (w : (h).Instance), (h).public w = x.1 →
    ∀ r : World, ¬ (∃ i, ProverCommitFuelJoin22.bad (oldBad w) (queries adv w) i r.coins) →
      ((rust).real h B outputs adv x w r).observerOracle =
        ((source).real h B outputs (RomObserverBin.observerMap rust observer_program adv) x w r.coins.1.1).observerOracle

theorem uniform_V037 (f : ModelCoins template outputs x → ℚ) :
    mean (fun s => f ((PV_RunJoin_WorldCoupling.cp runtime).toM s)) = mean f :=
  (PV_RunJoin_WorldCoupling.cp runtime).meanM f

def runJoin (premises : PV_RunJoin_Premises template outputs x runtime boundary)
    (adv : (rust).Adversary) (w : (h).Instance) (hw : (h).public w = x.1) :
    ProverCommitFuelJoin22.RunJoin
      (fun r => let v := (rust).real h B outputs adv x w r; (v,(rust).observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r; (v,(source).observe a v))
      (oldBad w) (queries adv w) where
  cp := PV_RunJoin_WorldCoupling.cp runtime
  agreement := by
    intro r hn
    have view := PV_RunJoin_AbstractEndpoint.complete_view_ext
      (premises.disclosed_V038 adv w hw r hn) (premises.observerOracle_V038 adv w hw r hn)
    apply Prod.ext view
    change (rust).observe adv _ = (rust).observe adv _
    exact congrArg ((rust).observe adv) view

theorem refinement_from_premises (premises : PV_RunJoin_Premises template outputs x runtime boundary) :
    PrivacyR1HeadlineDeployedReal.RustRealRefinement template outputs x rust observer_program := by
  intro adv w hw
  exact ⟨runJoin template outputs x runtime boundary premises adv w hw⟩

theorem privacy_headline_from_premises
    (premises : PV_RunJoin_Premises template outputs x runtime boundary)
 :
    (∀ (adv : (rust).Adversary) (w : (h).Instance), (h).public w = x.1 →
      |mean (realTest h B outputs rust adv x w) -
        mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
          (simE (h).transport B outputs x))| ≤
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100 := by
  exact PrivacyR1HeadlineDeployedReal.privacy_headline_deployed template outputs x rust observer_program
    (refinement_from_premises template outputs x runtime boundary premises)

#print axioms uniform_V037
#print axioms runJoin
#print axioms refinement_from_premises
#print axioms privacy_headline_from_premises
end R1Z.PV_RunJoin_Endpoint
