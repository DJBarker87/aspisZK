import R1Z.PV_Join_FixtureInputs
import R1Z.PV_RunJoin_DeployedFixtures
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_FixtureSelected
open Aeneas Aeneas.Std Result ProverRwFull
variable [ProverRwRngCaller.NativeTypes] [ProverRwRngCaller.ErasureFns]
local instance : CharP PrivacyR1AcctBasis.K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) PrivacyR1AcctBasis.K).injective AspisCircleGroupOrder.P

/-- The explicit selection premise is retained. This identifies the two
source-law caller inputs; it proves neither compiler success nor proof bytes. -/
theorem both_source {CommitHandle N C : Type} (base : ExternalTypes)
    (ops : PV_Join_LedgerSource.World base N C → @ExternalFuns (PV_Join_PublicCaller.native base))
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (selection : R0Z.ZkStatement.Statement PrivacyR1AcctBasis.K CommitHandle →
      (BuilderSource.prover (K := PrivacyR1AcctBasis.K)).Instance → PV_Src_NativeInput.Input)
    (a b : CommitHandle) (schedule : ProverCommitLedger36.Schedule) (unix : Bool)
    (address : PV_RunJoin_LedgerWorld.Address) :
    letI : ExternalTypes := PV_Join_PublicCaller.native base
    let transfer := selection (PV_RunJoin_DeployedFixtures.transferX a)
      PV_RunJoin_CanonicalFixtures.transfer
    let withdrawal := selection (PV_RunJoin_DeployedFixtures.withdrawalX b)
      PV_RunJoin_CanonicalFixtures.withdrawal
    PV_RunJoin_UnifiedRetry.BodySourceLaw
      (PV_RunJoin_LedgerSourceBody.sourceBody (PV_Join_FixtureInputs.inputs base ops hash transfer))
      (PV_RunJoin_LedgerBody.body schedule unix address (PV_Join_FixtureInputs.inputs base ops hash transfer)) ∧
    PV_RunJoin_UnifiedRetry.BodySourceLaw
      (PV_RunJoin_LedgerSourceBody.sourceBody (PV_Join_FixtureInputs.inputs base ops hash withdrawal))
      (PV_RunJoin_LedgerBody.body schedule unix address (PV_Join_FixtureInputs.inputs base ops hash withdrawal)) := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  exact ⟨PV_Join_FixtureInputs.body_source base ops hash _ schedule unix address,
    PV_Join_FixtureInputs.body_source base ops hash _ schedule unix address⟩

#print axioms both_source
end R1Z.PV_Join_FixtureSelected
