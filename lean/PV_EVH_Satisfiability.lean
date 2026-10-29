import PV_EVH_Deployed
/-! adopted by owner decision D502/D478. A conditional event-retaining headline.
The historical Result-only endpoint and the simulator are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVH_Satisfiability
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
open R1Z.PrivacyR1HeadlineDeployedEvents Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- adopted by owner decision D502/D478. Explicit MODEL instance only.
A nonempty failure prefix includes rejected attempts, oracle bytes, clock bytes,
stdout copies and a retained channel. The environment changes its time bytes.
This is not a native deployed execution or a discharged native link. -/
def trace (e : Bool) : NativeTrace Unit :=
  let time : PV_RJ4IDB.Bytes := [if e then 1 else 0]
  ⟨[.rejection 0,.count 1,.oracle [2] [3],.wall time,
    .returned time,.printed time time,.side [4] [5]],.failure [6]⟩

abbrev ModelCoins := (((source).RealRand × OracleAnswer) × ProverCommitFuelJoin22.Tape)

/-- adopted by owner decision D502/D478. All model data are explicit.
The op227 reference is the supplied operation itself, so its law is consistent
for ALL claims, including errors; this proves no deployed callback identity. -/
def modelRuntime (ops : ExternalFuns) (sem : host_semantic.SemanticOracle)
    (pt : Array aspis_core.field.QM31 10#usize) :
    Runtime (Public := Unit) (Signal := Bool) (Env := Bool) (A := Unit)
      (R := ModelCoins template outputs x) (S := ModelCoins template outputs x)
      (N := Bool × ModelCoins template outputs x) template outputs x where
  completion := ⟨fun _ e => e,fun _ _ e _ => trace e⟩
  publicInput := ()
  acquisition := id
  native := fun e _ _ _ => trace e
  signal := fun e _ _ _ => e
  toNative := fun _ _ _ => id
  toModel := fun _ _ _ => id
  published := fun _ => none
  compact := fun _ => none
  statementBytes := fun _ => none
  fileTrace := fun i => nativeFiles (trace i.1).events
  jsonStdout := fun i => (nativeJSON (trace i.1).events,nativeStdout (trace i.1).events)
  errorStderr := fun i => (nativeDiag2 (trace i.1).events,nativeDiag3 (trace i.1).events)
  countTrace := fun i => (nativeCounts (trace i.1).events,nativeRejections (trace i.1).events)
  timeTrace := fun i => nativeTimes (trace i.1).events
  oraclePrefix := fun i => nativeOracle (trace i.1).events
  retained := fun i => nativeSide (trace i.1).events
  actualProgram := fun adv i => adv.program (observe i.1 (trace i.1))
  ops := ops
  terminal := ops.op227
  semantic := fun _ => sem
  point := fun _ => pt

/-- adopted by owner decision D502/D478. Simultaneous satisfiability of EVERY
link of the adopted theorem, at exactly the same model instance. There are no
link hypotheses, no assumed privacy conclusion and no change of observer type. -/
theorem all_links (ops : ExternalFuns) (sem : host_semantic.SemanticOracle)
    (pt : Array aspis_core.field.QM31 10#usize) :
    Links template outputs x (modelRuntime template outputs x ops sem pt) := by
  constructor
  · intro i; rfl
  · intro i; rfl
  · intro i; rfl
  · intro i; rfl
  · intro i; rfl
  · intro i; rfl
  · intro i; rfl
  · intro i; rfl
  · intro i; rfl
  · intro e adv w; exact ⟨fun _ => rfl,fun _ => rfl⟩
  · intro e adv w s _; rfl
  · intro e adv w s _; rfl
  · intro e adv w s _; rfl
  · intro adv w _ value; rfl
  · intro value; rfl
  · intro e v history suffix
    change List.IsPrefix (trace e).events (trace e).events
    exact ⟨[],List.append_nil _⟩
  · intro adv i; rfl
  · intro i claims; rfl

/-- adopted by owner decision D502/D478. Existential form of ruling (v),
for exactly the full conjunction consumed by the adopted headline. -/
theorem simultaneously_satisfiable (ops : ExternalFuns) (sem : host_semantic.SemanticOracle)
    (pt : Array aspis_core.field.QM31 10#usize) :
    ∃ rt : Runtime (Public := Unit) (Signal := Bool) (Env := Bool) (A := Unit)
      (R := ModelCoins template outputs x) (S := ModelCoins template outputs x)
      (N := Bool × ModelCoins template outputs x) template outputs x,
      Links template outputs x rt :=
  ⟨modelRuntime template outputs x ops sem pt,all_links template outputs x ops sem pt⟩

/-- adopted by owner decision D502/D478. An inhabitant of the full adversary
carrier. No theorem restricts observers to this example. -/
def exampleObserver : Observer Bool Unit := ⟨fun _ => .done,fun _ => false⟩

#print axioms all_links
#print axioms simultaneously_satisfiable
#print axioms exampleObserver
end PV_EVH_Satisfiability
