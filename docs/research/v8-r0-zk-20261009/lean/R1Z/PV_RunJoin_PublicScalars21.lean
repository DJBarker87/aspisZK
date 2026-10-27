import R1Z.PV_RunJoin_SelectedPackage20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicScalars21
abbrev transfer := PV_Src_Public.canonicalPublic PV_RunJoin_RecordedTransfer.publicInput
abbrev withdrawal := PV_Src_Public.canonicalPublic PV_RunJoin_RecordedWithdrawal.publicInput

theorem transfer_variant : transfer.variant = (PV_RunJoin_FixtureRecords.fixturePublic false).variant := rfl
#print axioms transfer_variant
theorem withdrawal_variant : withdrawal.variant = (PV_RunJoin_FixtureRecords.fixturePublic true).variant := rfl
#print axioms withdrawal_variant
theorem transfer_asset : transfer.assetId = (PV_RunJoin_FixtureRecords.fixturePublic false).assetId := rfl
#print axioms transfer_asset
theorem withdrawal_asset : withdrawal.assetId = (PV_RunJoin_FixtureRecords.fixturePublic true).assetId := rfl
#print axioms withdrawal_asset
theorem transfer_amount : transfer.withdrawalAmount = (PV_RunJoin_FixtureRecords.fixturePublic false).withdrawalAmount := rfl
#print axioms transfer_amount
theorem withdrawal_amount : withdrawal.withdrawalAmount = (PV_RunJoin_FixtureRecords.fixturePublic true).withdrawalAmount := rfl
#print axioms withdrawal_amount
theorem withdrawal_recipient : withdrawal.recipient = (PV_RunJoin_FixtureRecords.fixturePublic true).recipient := rfl
#print axioms withdrawal_recipient
theorem transfer_index : transfer.nextPairIndex = (PV_RunJoin_FixtureRecords.fixturePublic false).nextPairIndex := rfl
#print axioms transfer_index
theorem withdrawal_index : withdrawal.nextPairIndex = (PV_RunJoin_FixtureRecords.fixturePublic true).nextPairIndex := rfl
#print axioms withdrawal_index
end R1Z.PV_RunJoin_PublicScalars21
