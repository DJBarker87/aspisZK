import PV_2TNV_PublicLiterals
import R1Z.PV_RunJoin_PathValues16
import R1Z.PV_RunJoin_OutputValues16
import R1Z.PV_RunJoin_FixtureNullifier
set_option autoImplicit false
noncomputable section
namespace AspisR1.PV_2TNV_TransferCore
open R0P R1Z AspisR1 AspisR1.SpendRelation
open PV_2TNV_PublicEncoding PV_2TNV_PublicLiterals
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

theorem anchor_eq : nativePublic.anchor = (PV_RunJoin_FixtureRecords.fixturePublic false).anchor := by
  rw [PV_2TNV_PublicLiterals.anchor]
  change d43 = merkleRootAux
    (noteCommitment (ownerKey (PV_RunJoin_FixtureRecords.digest 10)) 1000 77
      (PV_RunJoin_FixtureRecords.digest 100)) PV_RunJoin_FixtureRecords.path 24
  rw [PV_RunJoin_FixtureHashModel.input_commitment]
  exact PV_RunJoin_PathValues16.prefix_24.symm

theorem nullifier_eq : nativePublic.nullifier =
    (PV_RunJoin_FixtureRecords.fixturePublic false).nullifier := by
  rw [PV_2TNV_PublicLiterals.nullifier]
  change d44 = nullifierHash (PV_RunJoin_FixtureRecords.digest 10)
    (PV_RunJoin_FixtureRecords.digest 100)
  rw [PV_RunJoin_FixtureHashModel.nullifier]
  funext i
  fin_cases i <;> rfl

theorem asset_eq : nativePublic.assetId = (PV_RunJoin_FixtureRecords.fixturePublic false).assetId :=
  PV_2TNV_PublicLiterals.asset

theorem recipient_eq : nativePublic.recipient =
    (PV_RunJoin_FixtureRecords.fixturePublic false).recipient := by
  rw [PV_2TNV_PublicLiterals.recipient]
  change some d45 = some (noteCommitment (PV_RunJoin_FixtureRecords.digest 300)
    600 77 (PV_RunJoin_FixtureRecords.digest 400))
  rw [PV_RunJoin_OutputValues16.recipient]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem change_eq : nativePublic.change = (PV_RunJoin_FixtureRecords.fixturePublic false).change := by
  rw [PV_2TNV_PublicLiterals.change_value]
  change d46 = noteCommitment (PV_RunJoin_FixtureRecords.digest 500)
    400 77 (PV_RunJoin_FixtureRecords.digest 600)
  rw [PV_RunJoin_OutputValues16.transfer_change]
  funext i
  fin_cases i <;> rfl

/-- Transport the input/output core while retaining the new append obligation.
This is a helper, not a claimed wrapper-to-headline theorem. -/
theorem spendPlus (append : AppendBinding nativePublic) :
    BuilderSpendRelation.RspendPlus nativePublic (PV_RunJoin_FixtureRecords.witness false) := by
  obtain ⟨_,rel,conservation,changeLaw,variant,_⟩ := PV_RunJoin_FixtureRecords.spend false
  refine ⟨⟨⟨rfl,rfl⟩,?_,conservation,?_,?_,append⟩,?_⟩
  · exact {
      valid := rel.valid
      spendable := rel.spendable
      commitment := by rw [asset_eq]; exact rel.commitment
      sibling := rel.sibling
      nullifier := nullifier_eq.trans rel.nullifier
      membership := by rw [asset_eq,anchor_eq]; exact rel.membership }
  · unfold changeCommitment at *
    rw [change_eq,asset_eq]
    exact changeLaw
  · change nativePublic.recipient = some (recipientCommitment nativePublic _)
    change (PV_RunJoin_FixtureRecords.fixturePublic false).recipient =
      some (recipientCommitment (PV_RunJoin_FixtureRecords.fixturePublic false) _) at variant
    unfold recipientCommitment at *
    rw [recipient_eq,asset_eq]
    exact variant
  · intro _
    rw [change_eq]
    exact PV_RunJoin_TransferSentinel.nonzero

#print axioms anchor_eq
#print axioms nullifier_eq
#print axioms asset_eq
#print axioms recipient_eq
#print axioms change_eq
#print axioms spendPlus
end AspisR1.PV_2TNV_TransferCore
