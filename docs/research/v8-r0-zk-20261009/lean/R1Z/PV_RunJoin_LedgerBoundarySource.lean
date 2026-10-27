import R1Z.PV_RunJoin_LedgerBoundary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerBoundarySource
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


theorem source_fields
    (identity : ∀ h x w s, PV_RunJoin_MapErrInstalled.Identity ((inputs h x w).ops s))
    (x : Statement K CommitHandle) (d : PV_RunJoin_Boundary.Data runtime Context Rest)
    (h : HonestProver K) :
    (∀ w : h.Instance, h.public w = x.1 →
      PV_RunJoin_UnifiedRetry.BodySourceLaw
        ((PV_RunJoin_LedgerBoundary.boundary schedule unix address world policy inputs common disclosed oracle ideal x d).sourceBody h x w)
        ((runtime).body h x w)) ∧
    (∀ (s : State) k nonce next,
      (runtime).account.call_mut s k = .ok (nonce,next) → next.provider = s.provider) ∧
    (∀ w : h.Instance, h.public w = x.1 → ∀ secret (s next : State) status,
      (runtime).body h x w secret s = .ok (status,next) → next.provider = s.provider) := by
  refine ⟨fun w _ => PV_RunJoin_LedgerSourceBody.source_law schedule unix address (inputs h x w) (identity h x w),?_,?_⟩
  · intro s k nonce next run
    exact PV_RunJoin_SourceAccount.provider_frame policy s next k nonce run
  · intro w _ secret s next status run
    exact PV_RunJoin_LedgerSourceBody.provider_frame schedule unix address (inputs h x w) secret s next status run

#print axioms source_fields
end R1Z.PV_RunJoin_LedgerBoundarySource
