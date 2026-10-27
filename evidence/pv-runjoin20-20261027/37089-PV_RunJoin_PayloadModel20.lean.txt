import R1Z.PV_RunJoin_FixtureCorrespondence20
import R1Z.PV_RunJoin_NativeReturn20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PayloadModel20
open R0Z.WriterRefine PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M

theorem transfer : ∀ c r,
    liftU (K := M) (PV_Src_Forest_Columns.read PV_RunJoin_TransferPayload20.output.semantic_c1.c1 c r) =
      R0Z.BuilderModel.buildModel (PV_RunJoin_FixtureRecords.fixturePublic false)
        (toModel (wordWitness transferWitness)) c r :=
  PV_RunJoin_SourceModel20.transfer _ PV_RunJoin_FixtureCorrespondence20.transfer
#print axioms transfer

theorem withdrawal : ∀ c r,
    liftU (K := M) (PV_Src_Forest_Columns.read PV_RunJoin_WithdrawalPayload20.output.semantic_c1.c1 c r) =
      R0Z.BuilderModel.buildModel (PV_RunJoin_FixtureRecords.fixturePublic true)
        (toModel (wordWitness withdrawalWitness)) c r :=
  PV_RunJoin_SourceModel20.withdrawal _ PV_RunJoin_FixtureCorrespondence20.withdrawal
#print axioms withdrawal
end R1Z.PV_RunJoin_PayloadModel20
