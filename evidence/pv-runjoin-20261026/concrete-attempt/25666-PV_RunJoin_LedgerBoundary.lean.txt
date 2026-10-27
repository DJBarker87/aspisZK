import R1Z.PV_RunJoin_LedgerConstructor
import R1Z.PV_RunJoin_Boundary
import R1Z.PV_RunJoin_LedgerPublicShape
import R1Z.PV_RunJoin_SourceAccount
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerBoundary
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

/-- Candidate ledger interpreter boundary. The common reservation is fixed by
public statement; no witness or private compiled columns occur in that field.
Native world/effect/observer association is still a deployment obligation. -/
def boundary (x : Statement K CommitHandle) (d : PV_RunJoin_Boundary.Data runtime Context Rest) :
    PV_RunJoin_Boundary.Data runtime Context Rest :=
  {d with sourceBody := fun h x w => PV_RunJoin_LedgerSourceBody.sourceBody (inputs h x w)
          draw := ProverRwRngCaller.Tape.Insts.Prover_rw_rng_callerDraw64
          ledger := fun s => s.ledger.model
          reservation := fun secret s => PV_RunJoin_PublicDecision.decision
            ((common x).ops s) address ((common x).pub s) .S2 ((common x).hash s) secret.mask_nonce
          schedule := schedule
          unix := unix
          fault := fun _ s kind => schedule s.ledger.model.history.length kind s.ledger.model.history }

#print boundary
end R1Z.PV_RunJoin_LedgerBoundary
