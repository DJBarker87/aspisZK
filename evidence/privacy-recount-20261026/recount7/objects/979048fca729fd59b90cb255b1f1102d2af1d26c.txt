import R1Z.PV_RunJoin_OutputLift16
import R1Z.PV_RunJoin_OutputValues16
import R1Z.PV_RunJoin_TreeValue16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputChecks16
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M

theorem recipient_raw : recip_dr transferWitness transferPublic = ok PV_RunJoin_RecordedTransfer.publicRecord.recipient_commitment := by
  let W := PV_Src_Forest_PrimitiveArguments.wordWitness transferWitness
  let P := PV_Src_Forest_PrimitiveArguments.wordPublic transferPublic
  obtain ⟨d,hd,hl,hc⟩ := PV_RunJoin_OutputLift16.recipient W P (PV_RunJoin_FixtureRecords.base false)
    (by rfl) transfer_checked (by rfl)
  have owner : (toModel (K := M) W).recipientOwner = PV_RunJoin_FixtureRecords.digest 300 := by
    funext i; fin_cases i <;> rfl
  have salt : (toModel (K := M) W).recipientSalt = PV_RunJoin_FixtureRecords.digest 400 := by
    funext i; fin_cases i <;> rfl
  have value : (toModel (K := M) W).outputValue.val = 600 := rfl
  rw [owner,salt,value,show (PV_RunJoin_FixtureRecords.base false).assetId = 77 from rfl] at hl
  simp only [Nat.cast_ofNat] at hl
  rw [PV_RunJoin_OutputValues16.recipient] at hl
  have canonical : Canon8 PV_RunJoin_RecordedTransfer.publicRecord.recipient_commitment := by
    intro i hi; interval_cases i <;> decide
  have target_meaning : digK (K := M) PV_RunJoin_RecordedTransfer.publicRecord.recipient_commitment = R0P.digestOf PV_RunJoin_OutputModel16.s_32_23 := by
    funext i; fin_cases i <;> rfl
  have he : d = PV_RunJoin_RecordedTransfer.publicRecord.recipient_commitment :=
    PV_RunJoin_TreeValue16.unique d _ hc canonical (by rw [target_meaning]; exact hl)
  rw [PV_Src_Forest_AuxContent.recipient_digest]
  exact hd.trans (congrArg Result.ok he)

theorem recipient : CopyRecords.recipient ⟨transferWitness,transferPublic⟩ = ok PV_RunJoin_RecordedTransfer.publicRecord.recipient_commitment := by
  rw [CopyRecords.recipient,recipient_raw]
  with_unfolding_all rfl
#print axioms recipient_raw
#print axioms recipient

theorem transfer_change_raw : change_dr transferWitness transferPublic = ok PV_RunJoin_RecordedTransfer.publicRecord.change_commitment := by
  let W := PV_Src_Forest_PrimitiveArguments.wordWitness transferWitness
  let P := PV_Src_Forest_PrimitiveArguments.wordPublic transferPublic
  obtain ⟨d,hd,hl,hc⟩ := PV_RunJoin_OutputLift16.change_note W P (PV_RunJoin_FixtureRecords.base false)
    (by rfl) transfer_checked
  have owner : (toModel (K := M) W).changeOwner = PV_RunJoin_FixtureRecords.digest 500 := by
    funext i; fin_cases i <;> rfl
  have salt : (toModel (K := M) W).changeSalt = PV_RunJoin_FixtureRecords.digest 600 := by
    funext i; fin_cases i <;> rfl
  have value : (toModel (K := M) W).changeValue.val = 400 := rfl
  rw [owner,salt,value,show (PV_RunJoin_FixtureRecords.base false).assetId = 77 from rfl] at hl
  simp only [Nat.cast_ofNat] at hl
  rw [PV_RunJoin_OutputValues16.transfer_change] at hl
  have canonical : Canon8 PV_RunJoin_RecordedTransfer.publicRecord.change_commitment := by
    intro i hi; interval_cases i <;> decide
  have target_meaning : digK (K := M) PV_RunJoin_RecordedTransfer.publicRecord.change_commitment = R0P.digestOf PV_RunJoin_OutputModel16.s_35_23 := by
    funext i; fin_cases i <;> rfl
  have he : d = PV_RunJoin_RecordedTransfer.publicRecord.change_commitment :=
    PV_RunJoin_TreeValue16.unique d _ hc canonical (by rw [target_meaning]; exact hl)
  rw [PV_Src_Forest_AuxContent.change_digest]
  exact hd.trans (congrArg Result.ok he)

theorem transfer_change : CopyRecords.change ⟨transferWitness,transferPublic⟩ = ok PV_RunJoin_RecordedTransfer.publicRecord.change_commitment := by
  rw [CopyRecords.change,transfer_change_raw]
  with_unfolding_all rfl
#print axioms transfer_change_raw
#print axioms transfer_change

theorem withdrawal_change_raw : change_dr withdrawalWitness withdrawalPublic = ok PV_RunJoin_RecordedWithdrawal.publicRecord.change_commitment := by
  let W := PV_Src_Forest_PrimitiveArguments.wordWitness withdrawalWitness
  let P := PV_Src_Forest_PrimitiveArguments.wordPublic withdrawalPublic
  obtain ⟨d,hd,hl,hc⟩ := PV_RunJoin_OutputLift16.change_note W P (PV_RunJoin_FixtureRecords.base false)
    (by rfl) withdrawal_checked
  have owner : (toModel (K := M) W).changeOwner = PV_RunJoin_FixtureRecords.digest 700 := by
    funext i; fin_cases i <;> rfl
  have salt : (toModel (K := M) W).changeSalt = PV_RunJoin_FixtureRecords.digest 800 := by
    funext i; fin_cases i <;> rfl
  have value : (toModel (K := M) W).changeValue.val = 750 := rfl
  rw [owner,salt,value,show (PV_RunJoin_FixtureRecords.base false).assetId = 77 from rfl] at hl
  simp only [Nat.cast_ofNat] at hl
  rw [PV_RunJoin_OutputValues16.withdrawal_change] at hl
  have canonical : Canon8 PV_RunJoin_RecordedWithdrawal.publicRecord.change_commitment := by
    intro i hi; interval_cases i <;> decide
  have target_meaning : digK (K := M) PV_RunJoin_RecordedWithdrawal.publicRecord.change_commitment = R0P.digestOf PV_RunJoin_OutputModel16.s_38_23 := by
    funext i; fin_cases i <;> rfl
  have he : d = PV_RunJoin_RecordedWithdrawal.publicRecord.change_commitment :=
    PV_RunJoin_TreeValue16.unique d _ hc canonical (by rw [target_meaning]; exact hl)
  rw [PV_Src_Forest_AuxContent.change_digest]
  exact hd.trans (congrArg Result.ok he)

theorem withdrawal_change : CopyRecords.change ⟨withdrawalWitness,withdrawalPublic⟩ = ok PV_RunJoin_RecordedWithdrawal.publicRecord.change_commitment := by
  rw [CopyRecords.change,withdrawal_change_raw]
  with_unfolding_all rfl
#print axioms withdrawal_change_raw
#print axioms withdrawal_change
end R1Z.PV_RunJoin_OutputChecks16
