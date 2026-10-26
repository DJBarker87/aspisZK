import R1Z.PV_RunJoin_LedgerBoundary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerBoundaryLedger
open Aeneas Aeneas.Std Result
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.Batched
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N C Context Rest : Type}
variable (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (address : PV_RunJoin_LedgerWorld.Address)
    (world : PV_RunJoin_CompletedWorld.Data Coins N PV_RunJoin_LedgerWorld.World C)
    (policy : ProverRwEffectCallback.Account N)
    (inputs : (h : HonestProver K) → (x : Statement K CommitHandle) → h.Instance →
      PV_RunJoin_LedgerBody.Inputs N C)
    (common : Statement K CommitHandle → PV_RunJoin_LedgerBody.Inputs N C)
    (disclosed : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Result (PV_RunJoin_Deployed.Output N PV_RunJoin_LedgerWorld.World C) → View K CommitHandle Aux R1Bat)
    (oracle : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Result (PV_RunJoin_Deployed.Output N PV_RunJoin_LedgerWorld.World C) → List (Bytes × OracleAnswer))
    (ideal : (Challenges K → R0Z.JointView.Tape K F → View K CommitHandle Aux R1Bat) →
      R1Adv K CommitHandle Aux → Statement K CommitHandle → ROMView K CommitHandle Aux R1Bat)
local notation "runtime" => PV_RunJoin_LedgerConstructor.runtime schedule unix address world policy inputs disclosed oracle ideal
local notation "State" => PV_RunJoin_UnifiedRetry.State N PV_RunJoin_LedgerWorld.World C


theorem ledger_field (x : Statement K CommitHandle) (d : PV_RunJoin_Boundary.Data runtime Context Rest)
    (h : HonestProver K)
    (common_public : ∀ (w : h.Instance), h.public w = x.1 → ∀ s : State,
      (inputs h x w).ops s = (common x).ops s ∧
      (inputs h x w).pub s = (common x).pub s ∧
      (inputs h x w).hash s = (common x).hash s) :
    ∀ (w : h.Instance), h.public w = x.1 → ∀ secret (s next : State) status,
      (runtime).body h x w secret s = .ok (status,next) →
      (PV_RunJoin_LedgerBoundary.boundary schedule unix address world policy inputs common disclosed oracle ideal x d).ledger next =
        match (PV_RunJoin_LedgerBoundary.boundary schedule unix address world policy inputs common disclosed oracle ideal x d).reservation secret s with
        | none => (PV_RunJoin_LedgerBoundary.boundary schedule unix address world policy inputs common disclosed oracle ideal x d).ledger s
        | some path => (ProverCommitLedger36.reserve schedule unix path
            ((PV_RunJoin_LedgerBoundary.boundary schedule unix address world policy inputs common disclosed oracle ideal x d).ledger s)).2 := by
  intro w hw secret s next status run
  have shape := PV_RunJoin_LedgerPublicShape.ledger_public schedule unix address (inputs h x w) secret s next status run
  obtain ⟨ops_eq,pub_eq,hash_eq⟩ := common_public w hw s
  rw [ops_eq,pub_eq,hash_eq] at shape
  exact shape

#print axioms ledger_field
end R1Z.PV_RunJoin_LedgerBoundaryLedger
