import R1Z.PV_RunJoin_InstalledFamily
import R1Z.PV_RunJoin_DeployedFixtures
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureSelectedSources
open Aeneas Aeneas.Std Result ProverRwFull
local instance : ProverRwRngCaller.NativeTypes := PV_RunJoin_CallerWorld.nativeTypes
local instance : ProverRwRngCaller.ErasureFns := ⟨fun _ value => .ok value,fun _ value => .ok value⟩
variable {CommitHandle N C : Type}
local instance : CharP PrivacyR1AcctBasis.K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) PrivacyR1AcctBasis.K).injective AspisCircleGroupOrder.P

/-- Both release fixture fibres use exactly the selected compiler record in
both public and compiled inputs. This source theorem is independent of the
native compiler-success/admission and byte-association obligations. -/
theorem both_source (base : ExternalTypes)
    (ops : PV_RunJoin_NativeSelectedInputs.LedgerState base N C → @ExternalFuns (PDict_CodecDictionary.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : PV_RunJoin_InstalledFamily.Selection CommitHandle)
    (a b : CommitHandle) (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) :
    letI : ExternalTypes := PDict_CodecDictionary.native base
    let transfer := selection.selected BuilderSource.prover (PV_RunJoin_DeployedFixtures.transferX a)
      PV_RunJoin_CanonicalFixtures.transfer
    let withdrawal := selection.selected BuilderSource.prover (PV_RunJoin_DeployedFixtures.withdrawalX b)
      PV_RunJoin_CanonicalFixtures.withdrawal
    PV_RunJoin_UnifiedRetry.BodySourceLaw
      (PV_RunJoin_LedgerSourceBody.sourceBody (PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash transfer))
      (PV_RunJoin_LedgerBody.body schedule unix address (PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash transfer)) ∧
    PV_RunJoin_UnifiedRetry.BodySourceLaw
      (PV_RunJoin_LedgerSourceBody.sourceBody (PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash withdrawal))
      (PV_RunJoin_LedgerBody.body schedule unix address (PV_RunJoin_NativeSelectedInputs.ledgerInputs base ops hash withdrawal)) := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  exact ⟨PV_RunJoin_NativeSelectedInputs.full_ledger_source base ops hash _ schedule unix address,
    PV_RunJoin_NativeSelectedInputs.full_ledger_source base ops hash _ schedule unix address⟩

#print axioms both_source
end R1Z.PV_RunJoin_FixtureSelectedSources
