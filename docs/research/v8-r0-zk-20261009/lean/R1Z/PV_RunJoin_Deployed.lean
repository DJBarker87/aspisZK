import R1Z.PV_RunJoin_CompletedWorld
import R1Z.PV_RunJoin_UnifiedRetry
import R1Z.PrivacyR1HeadlineDeployedReal
/-! Effect-interpreted client instance. The initializer, source-body handler,
and observer decoder are DATA, whose native association remains explicit.
No native correctness follows merely from the name `rust`. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Deployed
open Aeneas Aeneas.Std Result ProverRwRngCaller
open R0Z R0Z.JointView R0Z.FsStatement
open R1Z.GamesR1 R1Z.Batched
local instance : NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
variable [ProverRwFull.ExternalTypes]

abbrev State := PV_RunJoin_UnifiedRetry.State
abbrev Output (N L C : Type) :=
  ProverCommitRetry34.Step (ProverCommitRetry34.Published ProverRwRetryModel.Proof) × State N L C

structure Runtime (CommitHandle Aux Coins N L C : Type) where
  world : PV_RunJoin_CompletedWorld.Data Coins N L C
  account : ProverRwEffectCallback.Account (State N L C)
  body : (h : HonestProver K) → Statement K CommitHandle → h.Instance →
    PV_RunJoin_UnifiedRetry.Body (State N L C)
  disclosed : R1Adv K CommitHandle Aux → Statement K CommitHandle →
    Result (Output N L C) → View K CommitHandle Aux R1Bat
  observerOracle : R1Adv K CommitHandle Aux → Statement K CommitHandle →
    Result (Output N L C) → List (Bytes × OracleAnswer)
  ideal : (Challenges K → R0Z.JointView.Tape K F → View K CommitHandle Aux R1Bat) →
    R1Adv K CommitHandle Aux → Statement K CommitHandle → ROMView K CommitHandle Aux R1Bat

variable {CommitHandle Aux Coins N L C : Type}
variable (runtime : Runtime CommitHandle Aux Coins N L C)

def initialState (r : Coins) : State N L C :=
  ⟨PV_RunJoin_CompletedWorld.provider runtime.world r,
    runtime.world.policy r,runtime.world.ledger r,runtime.world.body r⟩

abbrev World := PV_RunJoin_FiniteGraph.World (initialState runtime)

def coordinates : World runtime ≃ Coins :=
  PV_RunJoin_FiniteGraph.coordinates (initialState runtime)

def execute (h : HonestProver K) (x : Statement K CommitHandle) (w : h.Instance)
    (r : World runtime) : Result (Output N L C) :=
  PV_RunJoin_UnifiedRetry.client runtime.account (runtime.body h x w) r.state

def rust : FSExperiments K CommitHandle Aux R1Bat F where
  Adversary := R1Adv K CommitHandle Aux
  RealRand := World runtime
  IdealRand := Unit
  real := fun h _ _ adv x w r =>
    let out := execute runtime h x w r
    ⟨runtime.disclosed adv x out,runtime.observerOracle adv x out⟩
  ideal := fun sim adv x _ => runtime.ideal sim adv x
  observe := fun adv view => adv.decide view

instance finite [Fintype Coins] : Fintype (rust runtime).RealRand :=
  inferInstanceAs (Fintype (World runtime))
instance nonempty [Nonempty Coins] : Nonempty (rust runtime).RealRand :=
  inferInstanceAs (Nonempty (World runtime))

def observer_program : (rust runtime).Adversary → View K CommitHandle Aux R1Bat →
    List (Bytes × OracleAnswer) → OProg := fun adv => adv.prog

theorem complete_decision (adv : (rust runtime).Adversary) (view : ROMView K CommitHandle Aux R1Bat) :
    (rust runtime).observe adv view = adv.decide view := rfl

theorem observer_exact (adv : (rust runtime).Adversary) :
    RomObserverBin.observerMap (rust runtime) (observer_program runtime) adv = adv := by
  cases adv
  rfl

#print axioms initialState
#print axioms coordinates
#print axioms execute
#print axioms rust
#print axioms finite
#print axioms nonempty
#print axioms complete_decision
#print axioms observer_exact
end R1Z.PV_RunJoin_Deployed
