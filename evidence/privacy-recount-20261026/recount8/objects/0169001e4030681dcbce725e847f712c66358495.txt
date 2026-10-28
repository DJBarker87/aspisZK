import R1Z.PrivacyR1HeadlineDeployedReal
import R1Z.PV_RunJoin_Coupling
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AbstractEndpoint
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


/-! Conditional composition only. `rust`, padding and the model projection are
still parameters. In particular this is NOT a deployed-source certificate.
V045/V047 cannot be discharged by packaging the remaining view laws. -/

abbrev ModelCoins := (((source).RealRand × OracleAnswer) × ProverCommitFuelJoin22.Tape)
variable {Padding : Type} [Fintype Padding] [Nonempty Padding]
variable (toModel : (adv : rust.Adversary) → (w : (h).Instance) →
  rust.RealRand × Padding → ModelCoins template outputs x)

abbrev modelView (adv : rust.Adversary) (w : (h).Instance) (r : (source).RealRand) :=
  (source).real h B outputs (RomObserverBin.observerMap rust observer_program adv) x w r

abbrev oldBad (w : (h).Instance) := QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w
abbrev queries (adv : rust.Adversary) (w : (h).Instance) :=
  PrivacyR1HeadlineDeployedReal.realSeedQueries template outputs x rust observer_program adv w

/-- Original quantifiers and arbitrary common coupling, with complete view
agreement. No product-carrier or coordinate-bijection restriction. -/
def ViewRefinement : Prop :=
  ∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (rust.real h B outputs adv x w)
      ((source).real h B outputs (RomObserverBin.observerMap rust observer_program adv) x w)
      (oldBad template outputs x w)
      (queries template outputs x rust observer_program adv w))

/-- The exact original RunJoin premise is equivalent to complete VIEW
refinement: decision equality follows for the unchanged complete observer.
The SAME witness coupling is retained in both directions. -/
theorem refinement_iff_view :
    PrivacyR1HeadlineDeployedReal.RustRealRefinement template outputs x rust observer_program ↔
      ViewRefinement template outputs x rust observer_program := by
  constructor
  · intro refinement adv w hw
    obtain ⟨join⟩ := refinement adv w hw
    exact ⟨{ cp := join.cp
             agreement := fun s hn => congrArg Prod.fst (join.agreement s hn) }⟩
  · intro refinement adv w hw
    obtain ⟨join⟩ := refinement adv w hw
    refine ⟨{ cp := join.cp, agreement := ?_ }⟩
    intro s hn
    have view := join.agreement s hn
    apply Prod.ext view
    change rust.observe adv _ = rust.observe adv _
    exact congrArg (rust.observe adv) view

/-- Explicit residual laws for a common PRODUCT sampling carrier. Padding
and the projection are separate data. V045 and V047 remain outside this
abstract transport theorem and are NOT removed. -/
structure PV_RunJoin_Premises : Prop where
  uniform_V037 : ∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    ∀ f : ModelCoins template outputs x → ℚ,
      mean (fun s => f (toModel adv w s)) = mean f
  disclosed_V038 : ∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    ∀ r, ¬ (∃ i, ProverCommitFuelJoin22.bad (oldBad template outputs x w)
      (queries template outputs x rust observer_program adv w) i (toModel adv w r)) →
      (rust.real h B outputs adv x w r.1).disclosed =
        (modelView template outputs x rust observer_program adv w (toModel adv w r).1.1).disclosed
  observerOracle_V038 : ∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    ∀ r, ¬ (∃ i, ProverCommitFuelJoin22.bad (oldBad template outputs x w)
      (queries template outputs x rust observer_program adv w) i (toModel adv w r)) →
      (rust.real h B outputs adv x w r.1).observerOracle =
        (modelView template outputs x rust observer_program adv w (toModel adv w r).1.1).observerOracle

theorem complete_view_ext {a b : ROMView K CommitHandle Aux R1Bat}
    (disclosed : a.disclosed = b.disclosed) (oracle : a.observerOracle = b.observerOracle) :
    a = b := by
  cases a
  cases b
  cases disclosed
  cases oracle
  rfl

omit [Fintype rust.RealRand] [Nonempty rust.RealRand] in
/-- Exact equivalence, in both directions, for the ORIGINAL complete
observer. No observer restriction or bad-event enlargement is involved. -/
theorem complete_observer_pair_iff (adv : rust.Adversary)
    (rv mv : ROMView K CommitHandle Aux R1Bat) :
    (rv, rust.observe adv rv) =
      (mv, (source).observe (RomObserverBin.observerMap rust observer_program adv) mv) ↔
      rv.disclosed = mv.disclosed ∧ rv.observerOracle = mv.observerOracle := by
  constructor
  · intro same
    have view : rv = mv := congrArg Prod.fst same
    exact ⟨congrArg ROMView.disclosed view, congrArg ROMView.observerOracle view⟩
  · rintro ⟨disclosed,oracle⟩
    have view := complete_view_ext disclosed oracle
    cases view
    rfl

/-- The complete decision needs no independent equation once the WHOLE view
is equal: observerMap preserves the exact original decision. -/
def runJoin
    (premises : PV_RunJoin_Premises template outputs x rust observer_program toModel)
    (adv : rust.Adversary) (w : (h).Instance) (hw : (h).public w = x.1) :
    ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (oldBad template outputs x w)
      (queries template outputs x rust observer_program adv w) where
  cp := PV_RunJoin_Coupling.projection_cp (toModel adv w) (premises.uniform_V037 adv w hw)
  agreement := by
    intro r hn
    have view := complete_view_ext
      (premises.disclosed_V038 adv w hw r hn)
      (premises.observerOracle_V038 adv w hw r hn)
    apply Prod.ext view
    change rust.observe adv _ = rust.observe adv _
    exact congrArg (rust.observe adv) view

theorem refinement_from_premises
    (premises : PV_RunJoin_Premises template outputs x rust observer_program toModel) :
    PrivacyR1HeadlineDeployedReal.RustRealRefinement template outputs x rust observer_program := by
  intro adv w hw
  exact ⟨runJoin template outputs x rust observer_program toModel premises adv w hw⟩

theorem privacy_headline_from_premises
    (premises : PV_RunJoin_Premises template outputs x rust observer_program toModel)
 :
    (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
      |mean (realTest h B outputs rust adv x w) -
        mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
          (simE (h).transport B outputs x))| ≤
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100 := by
  exact PrivacyR1HeadlineDeployedReal.privacy_headline_deployed template outputs x rust observer_program
    (refinement_from_premises template outputs x rust observer_program toModel premises)

#print axioms refinement_iff_view
#print axioms complete_observer_pair_iff
#print axioms complete_view_ext
#print axioms runJoin
#print axioms refinement_from_premises
#print axioms privacy_headline_from_premises
end R1Z.PV_RunJoin_AbstractEndpoint
