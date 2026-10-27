import R1Z.PrivacyR1HeadlineDeployedReal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_Endpoint
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

variable {E : Type}
variable (failure : E → rust.Adversary → ROMView K CommitHandle Aux R1Bat)

def realTestB (signal : Option E) (adv : rust.Adversary) (w : (h).Instance) :
    rust.RealRand → ℚ :=
  match signal with
  | none => realTest h B outputs rust adv x w
  | some e => fun _ => bit (rust.observe adv (failure e adv))

def idealTestSB (signal : Option E) (adv : rust.Adversary) :
    (source).IdealRand → ℚ :=
  match signal with
  | none => idealTestS source (RomObserverBin.observerMap rust observer_program adv) x
      (simE (h).transport B outputs x)
  | some e => fun _ => bit (rust.observe adv (failure e adv))

theorem privacy_headline_deployed_B
    (refinement : PrivacyR1HeadlineDeployedReal.RustRealRefinement template outputs x rust observer_program)
 (signal : Option E) :
    (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
      |mean (realTestB outputs x rust failure signal adv w) -
        mean (idealTestSB template outputs x rust observer_program failure signal adv)| ≤
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge)) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100 := by
  have old := PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
    template outputs x rust observer_program refinement
  refine ⟨?_, old.2⟩
  intro adv w hw
  cases signal with
  | none => exact old.1 adv w hw
  | some e =>
    simp only [realTestB, idealTestSB, mean_const, sub_self, abs_zero]
    exact (abs_nonneg _).trans (old.1 adv w hw)

#check @PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
#check @privacy_headline_deployed_B
#print axioms realTestB
#print axioms idealTestSB
#print axioms privacy_headline_deployed_B
end R1Z.PV_OptB_Endpoint
