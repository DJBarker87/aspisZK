import R1Z.PV_RunJoin_SourceConstructor
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_SourceFields
open Aeneas Aeneas.Std Result
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.Batched
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N C : Type}
abbrev State (N C : Type) := PV_RunJoin_UnifiedRetry.State N ProverRwRetryModel.Store C

/-- The constructor installs exactly its supplied observation functions.
This forwarding identity proves no native association for those parameters. -/
theorem fields
    (world : PV_RunJoin_CompletedWorld.Data Coins N ProverRwRetryModel.Store C)
    (policy : ProverRwEffectCallback.Account N)
    (inputs : (h : HonestProver K) → (x : Statement K CommitHandle) → h.Instance →
      PV_RunJoin_PureSourceLift.Inputs N C)
    (disclosed : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Result (PV_RunJoin_Deployed.Output N ProverRwRetryModel.Store C) → View K CommitHandle Aux R1Bat)
    (oracle : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Result (PV_RunJoin_Deployed.Output N ProverRwRetryModel.Store C) → List (Bytes × OracleAnswer))
    (ideal : (Challenges K → R0Z.JointView.Tape K F → View K CommitHandle Aux R1Bat) →
      R1Adv K CommitHandle Aux → Statement K CommitHandle → ROMView K CommitHandle Aux R1Bat) :
    (PV_RunJoin_SourceConstructor.runtime world policy inputs disclosed oracle ideal).disclosed = disclosed ∧
    (PV_RunJoin_SourceConstructor.runtime world policy inputs disclosed oracle ideal).observerOracle = oracle := ⟨rfl,rfl⟩
#print axioms fields
end R1Z.PV_RJDec_SourceFields
