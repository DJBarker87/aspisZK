import R1Z.PrivacyR1HeadlineDeployedReal
import R1Z.PV_L2_Premises
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace R1Z.PV_L2_HeadlineJoint
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


variable (adv : rust.Adversary) (w : (h).Instance)
local notation "observer" => RomObserverBin.observerMap rust observer_program adv
local notation "runtimeView" => (fun r =>
  (rust.real h B outputs adv x w r,rust.observe adv (rust.real h B outputs adv x w r)))
local notation "modelView" => (fun r =>
  ((source).real h B outputs observer x w r,
    (source).observe observer ((source).real h B outputs observer x w r)))
local notation "oldBad" => QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w
local notation "queries" => PrivacyR1HeadlineDeployedReal.realSeedQueries template outputs x rust observer_program adv w

abbrev Join := ProverCommitFuelJoin22.RunJoin runtimeView modelView oldBad queries

theorem original_refinement
    (refinement : PrivacyR1HeadlineDeployedReal.RustRealRefinement template outputs x rust observer_program)
    (hpublic : (h).public w=x.1) :
    Nonempty (Join template outputs x rust observer_program adv w) :=
  refinement adv w hpublic

variable {Proof Obs : Type}
variable (realRun : rust.RealRand → PV_L2_F3FullRetry.Run Proof)
    (modelRun : (source).RealRand → PV_L2_F3FullRetry.Run Proof)
    (realRows : rust.RealRand → PV_L2_Premises.Row → Obs)
    (modelRows : (source).RealRand → PV_L2_Premises.Row → Obs)

/-- Exact endpoint realBad and its existing seed/fuel augmentation. Every
row field is on the ORIGINAL source/runtime coupling; no row gets a new
marginal coupling. This still requires concrete native row instances and
subsequent source-to-simE absorption of the whole run. -/
def extend_actual (join : Join template outputs x rust observer_program adv w)
    (p : PV_L2_Premises.PV_L2_Premises join realRun modelRun realRows modelRows) :
    ProverCommitFuelJoin22.RunJoin
      (fun r => (runtimeView r,realRun r,realRows r))
      (fun r => (modelView r,modelRun r,modelRows r)) oldBad queries :=
  PV_L2_Premises.extend join realRun modelRun realRows modelRows p

theorem same_coupling (join : Join template outputs x rust observer_program adv w)
    (p : PV_L2_Premises.PV_L2_Premises join realRun modelRun realRows modelRows) :
    (extend_actual template outputs x rust observer_program adv w
      realRun modelRun realRows modelRows join p).cp = join.cp := rfl

#print axioms original_refinement
#print axioms extend_actual
#print axioms same_coupling
end R1Z.PV_L2_HeadlineJoint
