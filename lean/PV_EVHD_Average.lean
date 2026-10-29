import PV_EVHD_Headline
/-! EXPERIMENTAL, NOT ADOPTED (D478). A conditional event-retaining headline.
No deployed Runtime, simulator, observer, bound or trust field is edited. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVHD_Average
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



open PV_RJ4IDB PV_EVHD_Interface PV_EVHD_Headline

/-- EXPERIMENTAL: shared public noise is averaged jointly, without conditioning
on success, a failure code, or a favourable clock value. -/
theorem average_bound {E R I : Type} [Fintype E] [Nonempty E]
    [Fintype R] [Fintype I] (real : E → R → ℚ) (ideal : E → I → ℚ) (ε : ℚ)
    (per_env : ∀ e, |mean (real e) - mean (ideal e)| ≤ ε) :
    |mean (fun p : E × R => real p.1 p.2) -
      mean (fun p : E × I => ideal p.1 p.2)| ≤ ε := by
  rw [R0Z.LawTransport.mean_product, R0Z.LawTransport.mean_product,
    R0Z.FsGood.mean_sub]
  exact (R0Z.FsGood.abs_mean_le _).trans
    ((R0Z.FsAbortBounds.mean_mono' _ _ per_env).trans_eq (R0Z.FsAbort.mean_const ε))

variable {Public Signal Env A R : Type} [Fintype R] [Nonempty R]
    [Fintype Env] [Nonempty Env]
    (completion : Completion Public Signal Env (ROMView K CommitHandle Aux R1Bat) A)
    (pubData : Public)
    (native : Env → Observer Signal A → (h).Instance → R → NativeTrace A)
    (nativeSignal : Env → Observer Signal A → (h).Instance → R → Signal)

/-- EXPERIMENTAL real experiment with public environment marginal. Native
association with this product is OPEN; it is not inferred from signal marginals. -/
def realExperiment (adv : Observer Signal A) (w : (h).Instance)
    (r : Env × R) : Signal × Observation A :=
  PV_EVHD_Headline.real r.1 native nativeSignal adv w r.2

/-- EXPERIMENTAL joint ideal experiment: sample public environment/noise and
simE coins, then generate all ordered channels using the same completion. -/
def idealExperiment (adv : Observer Signal A) (r : Env × (source).IdealRand) :
    Signal × Observation A :=
  PV_EVHD_Headline.ideal template outputs x completion pubData r.1 adv r.2

theorem draft_headline_joint
    (links : ∀ env (adv : Observer Signal A) (w : (h).Instance), (h).public w = x.1 →
      Links template outputs x completion pubData env native nativeSignal adv w)
    (adv : Observer Signal A) (w : (h).Instance) (hw : (h).public w = x.1) :
    |mean (fun r => bit (adv.decide (realExperiment native nativeSignal adv w r))) -
      mean (fun r => bit (adv.decide
        (idealExperiment template outputs x completion pubData adv r)))| ≤
      PV_EVHD_Headline.bound template outputs x := by
  apply average_bound
  intro env
  exact (PV_EVHD_Headline.draft_headline template outputs x completion pubData env
    native nativeSignal (links env)).1 adv w hw

#print axioms average_bound
#print axioms draft_headline_joint
end PV_EVHD_Average
