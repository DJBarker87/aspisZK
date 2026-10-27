import R1Z.PV_RunJoin_WithdrawalWitness20
import R1Z.PV_RunJoin_TransferSentinel
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AdmittedPayload20
open R0Z.WriterRefine PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M

theorem transfer_trace : ∀ c r,
    liftU (K := M) (PV_Src_Forest_Columns.read PV_RunJoin_TransferPayload20.output.semantic_c1.c1 c r) =
      R0Z.BuilderModel.buildModel (PV_RunJoin_FixtureRecords.fixturePublic false)
        (BuilderSpendRelation.modelWitness (PV_RunJoin_FixtureRecords.witness false)) c r := by
  intro c r
  rw [PV_RunJoin_PayloadModel20.transfer,PV_RunJoin_TransferWitness20.source]
#print axioms transfer_trace

theorem transfer : ∃ w : AspisR1.SpendRelation.Wspend,
    BuilderSpendRelation.RspendPlus (PV_RunJoin_FixtureRecords.fixturePublic false) w ∧
    ∀ c r, liftU (K := M) (PV_Src_Forest_Columns.read PV_RunJoin_TransferPayload20.output.semantic_c1.c1 c r) =
      R0Z.BuilderModel.buildModel (PV_RunJoin_FixtureRecords.fixturePublic false)
        (BuilderSpendRelation.modelWitness w) c r := by
  refine ⟨PV_RunJoin_FixtureRecords.witness false,?_,transfer_trace⟩
  exact PV_RunJoin_FixtureRecords.transfer_spendPlus PV_RunJoin_TransferSentinel.nonzero
#print axioms transfer

theorem withdrawal_trace : ∀ c r,
    liftU (K := M) (PV_Src_Forest_Columns.read PV_RunJoin_WithdrawalPayload20.output.semantic_c1.c1 c r) =
      R0Z.BuilderModel.buildModel (PV_RunJoin_FixtureRecords.fixturePublic true)
        (BuilderSpendRelation.modelWitness (PV_RunJoin_WithdrawalWitness20.witness)) c r := by
  intro c r
  rw [PV_RunJoin_PayloadModel20.withdrawal,PV_RunJoin_WithdrawalWitness20.source]
#print axioms withdrawal_trace

theorem withdrawal : ∃ w : AspisR1.SpendRelation.Wspend,
    BuilderSpendRelation.RspendPlus (PV_RunJoin_FixtureRecords.fixturePublic true) w ∧
    ∀ c r, liftU (K := M) (PV_Src_Forest_Columns.read PV_RunJoin_WithdrawalPayload20.output.semantic_c1.c1 c r) =
      R0Z.BuilderModel.buildModel (PV_RunJoin_FixtureRecords.fixturePublic true)
        (BuilderSpendRelation.modelWitness w) c r := by
  refine ⟨PV_RunJoin_WithdrawalWitness20.witness,?_,withdrawal_trace⟩
  exact PV_RunJoin_WithdrawalWitness20.admission
#print axioms withdrawal
end R1Z.PV_RunJoin_AdmittedPayload20
