import R1Z.PV_RunJoin_Deployed
import R1Z.PV_RunJoin_LedgerSourceBody
import R1Z.PV_RunJoin_SourceAccount
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerConstructor
open Aeneas Aeneas.Std Result
open R0P R0Z R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.Batched
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N C : Type}
abbrev State (N C : Type) := PV_RunJoin_UnifiedRetry.State N PV_RunJoin_LedgerWorld.World C

/-- Partially constructed operational runtime. All remaining DATA parameters
are deliberately explicit: world initialization, account policy, native
dictionary/public/compiled/hash inputs, both complete observer decoders and
the ideal handler. Giving this function a name does not remove those inputs.
The generic body projects to the full emitted prove_masked_attempt under its installed op12 law; filesystem/oracle
effect adequacy of its pure dictionary is still unproved. -/
def runtime
    (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (address : PV_RunJoin_LedgerWorld.Address)
    (world : PV_RunJoin_CompletedWorld.Data Coins N PV_RunJoin_LedgerWorld.World C)
    (policy : ProverRwEffectCallback.Account N)
    (inputs : (h : HonestProver K) → (x : Statement K CommitHandle) → h.Instance →
      PV_RunJoin_LedgerBody.Inputs N C)
    (disclosed : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Result (PV_RunJoin_Deployed.Output N PV_RunJoin_LedgerWorld.World C) → View K CommitHandle Aux R1Bat)
    (oracle : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Result (PV_RunJoin_Deployed.Output N PV_RunJoin_LedgerWorld.World C) → List (Bytes × OracleAnswer))
    (ideal : (Challenges K → R0Z.JointView.Tape K F → View K CommitHandle Aux R1Bat) →
      R1Adv K CommitHandle Aux → Statement K CommitHandle → ROMView K CommitHandle Aux R1Bat) :
    PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N PV_RunJoin_LedgerWorld.World C where
  world := world
  account := PV_RunJoin_SourceAccount.account policy
  body := fun h x w => PV_RunJoin_LedgerBody.body schedule unix address (inputs h x w)
  disclosed := disclosed
  observerOracle := oracle
  ideal := ideal

#print runtime
end R1Z.PV_RunJoin_LedgerConstructor
