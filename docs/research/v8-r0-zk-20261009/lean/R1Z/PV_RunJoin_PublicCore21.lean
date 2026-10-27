import R1Z.PV_RunJoin_SelectedPackage20
import R1Z.PV_RunJoin_PathChecks16
import R1Z.PV_RunJoin_OutputValues16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicCore21
open R0Z.WriterRefine
local notation "M" => PV_RunJoin_FixtureRecords.M
attribute [local irreducible] R0P.poseidonPermutation R0P.nodeCompress
abbrev transfer := PV_Src_Public.canonicalPublic PV_RunJoin_RecordedTransfer.publicInput
abbrev withdrawal := PV_Src_Public.canonicalPublic PV_RunJoin_RecordedWithdrawal.publicInput

theorem transfer_anchor : transfer.anchor = (PV_RunJoin_FixtureRecords.fixturePublic false).anchor := by
  change digK (K := M) PV_RunJoin_RecordedTransfer.publicRecord.anchor_root =
    R0P.merkleRootAux (R0P.noteCommitment (R0P.ownerKey (PV_RunJoin_FixtureRecords.digest 10))
      1000 77 (PV_RunJoin_FixtureRecords.digest 100)) PV_RunJoin_FixtureRecords.path 24
  rw [PV_RunJoin_FixtureHashModel.input_commitment]
  exact PV_RunJoin_PathChecks16.anchor_value.symm
#print axioms transfer_anchor

theorem transfer_nullifier : transfer.nullifier = (PV_RunJoin_FixtureRecords.fixturePublic false).nullifier := by
  change digK (K := M) PV_RunJoin_RecordedTransfer.publicRecord.nullifier =
    R0P.nullifierHash (PV_RunJoin_FixtureRecords.digest 10) (PV_RunJoin_FixtureRecords.digest 100)
  rw [PV_RunJoin_FixtureHashModel.nullifier]
  funext i; fin_cases i <;> rfl
#print axioms transfer_nullifier

theorem transfer_recipient : transfer.recipient = (PV_RunJoin_FixtureRecords.fixturePublic false).recipient := by
  change some (digK (K := M) PV_RunJoin_RecordedTransfer.publicRecord.recipient_commitment) =
    some (R0P.noteCommitment (PV_RunJoin_FixtureRecords.digest 300) 600 77 (PV_RunJoin_FixtureRecords.digest 400))
  rw [PV_RunJoin_OutputValues16.recipient]
  congr 1
  funext i; fin_cases i <;> rfl
#print axioms transfer_recipient

theorem transfer_change : transfer.change = (PV_RunJoin_FixtureRecords.fixturePublic false).change := by
  change digK (K := M) PV_RunJoin_RecordedTransfer.publicRecord.change_commitment =
    R0P.noteCommitment (PV_RunJoin_FixtureRecords.digest 500) 400 77 (PV_RunJoin_FixtureRecords.digest 600)
  rw [PV_RunJoin_OutputValues16.transfer_change]
  funext i; fin_cases i <;> rfl
#print axioms transfer_change

theorem withdrawal_anchor : withdrawal.anchor = (PV_RunJoin_FixtureRecords.fixturePublic true).anchor := by
  change digK (K := M) PV_RunJoin_RecordedWithdrawal.publicRecord.anchor_root =
    R0P.merkleRootAux (R0P.noteCommitment (R0P.ownerKey (PV_RunJoin_FixtureRecords.digest 10))
      1000 77 (PV_RunJoin_FixtureRecords.digest 100)) PV_RunJoin_FixtureRecords.path 24
  have hr : PV_RunJoin_RecordedWithdrawal.publicRecord.anchor_root =
      PV_RunJoin_RecordedTransfer.publicRecord.anchor_root := rfl
  rw [hr,PV_RunJoin_FixtureHashModel.input_commitment]
  exact PV_RunJoin_PathChecks16.anchor_value.symm
#print axioms withdrawal_anchor

theorem withdrawal_nullifier : withdrawal.nullifier = (PV_RunJoin_FixtureRecords.fixturePublic true).nullifier := by
  change digK (K := M) PV_RunJoin_RecordedWithdrawal.publicRecord.nullifier =
    R0P.nullifierHash (PV_RunJoin_FixtureRecords.digest 10) (PV_RunJoin_FixtureRecords.digest 100)
  rw [PV_RunJoin_FixtureHashModel.nullifier]
  funext i; fin_cases i <;> rfl
#print axioms withdrawal_nullifier

theorem withdrawal_change : withdrawal.change = (PV_RunJoin_FixtureRecords.fixturePublic true).change := by
  change digK (K := M) PV_RunJoin_RecordedWithdrawal.publicRecord.change_commitment =
    R0P.noteCommitment (PV_RunJoin_FixtureRecords.digest 700) 750 77 (PV_RunJoin_FixtureRecords.digest 800)
  rw [PV_RunJoin_OutputValues16.withdrawal_change]
  funext i; fin_cases i <;> rfl
#print axioms withdrawal_change
end R1Z.PV_RunJoin_PublicCore21
