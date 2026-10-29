import R1Z.PV_RunJoin_InstalledEndpoint
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_InstalledFields
open Aeneas Aeneas.Std Result ProverRwFull
open R0P R0Z R0Z.FsStatement R0Z.JointView R1Z.GamesR1 R1Z.Batched
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {CommitHandle Aux Coins N C : Type}

/-- Dictionary specialization still forwards its complete observation inputs.
Neither equality identifies those inputs with native disclosed/oracle code. -/
theorem fields (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Statement K CommitHandle → Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : PV_RunJoin_InstalledFamily.Selection CommitHandle)
    (schedule : ProverCommitLedger36.Schedule) (unix : Bool) (address : PV_RunJoin_LedgerWorld.Address) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    (world : PV_RunJoin_CompletedWorld.Data Coins N PV_RunJoin_LedgerWorld.World C) →
    (policy : ProverRwEffectCallback.Account N) →
    (disclosed : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Result (PV_RunJoin_Deployed.Output N PV_RunJoin_LedgerWorld.World C) → View K CommitHandle Aux R1Bat) →
    (oracle : R1Adv K CommitHandle Aux → Statement K CommitHandle →
      Result (PV_RunJoin_Deployed.Output N PV_RunJoin_LedgerWorld.World C) → List (Bytes × OracleAnswer)) →
    (ideal : (Challenges K → Tape K F → View K CommitHandle Aux R1Bat) →
      R1Adv K CommitHandle Aux → Statement K CommitHandle → ROMView K CommitHandle Aux R1Bat) →
    let r := PV_RunJoin_InstalledEndpoint.runtime base ops hash selection schedule unix address
      world policy disclosed oracle ideal
    r.disclosed = disclosed ∧ r.observerOracle = oracle := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  intro world policy disclosed oracle ideal
  exact ⟨rfl,rfl⟩
#print axioms fields
end R1Z.PV_RJDec_InstalledFields
