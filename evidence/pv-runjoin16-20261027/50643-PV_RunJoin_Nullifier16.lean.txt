import R1Z.PV_RunJoin_NullifierLift16
import R1Z.PV_RunJoin_FixtureReturns16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Nullifier16
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M

theorem transfer_raw :
    note_digest_r transferWitness transferPublic 26#usize =
      ok PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
  let W := PV_Src_Forest_PrimitiveArguments.wordWitness transferWitness
  let P := PV_Src_Forest_PrimitiveArguments.wordPublic transferPublic
  obtain ⟨d,hd,hl,hc⟩ := PV_RunJoin_NullifierLift16.nullifier W P (PV_RunJoin_FixtureRecords.base false)
    (by rfl) transfer_checked
  have sk : (toModel (K := M) W).sk = PV_RunJoin_FixtureRecords.digest 10 := by
    funext i; fin_cases i <;> rfl
  have salt : (toModel (K := M) W).salt = PV_RunJoin_FixtureRecords.digest 100 := by
    funext i; fin_cases i <;> rfl
  rw [sk,salt,PV_RunJoin_FixtureHashModel.nullifier] at hl
  have canonical : Canon8 PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
    intro j hj; interval_cases j <;> decide
  have he : d = PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    have bound : j < 8 := by simpa using hj
    apply PV_RunJoin_LeafLift16.word_injective (hc j hj) (canonical j bound)
    have h := hl ⟨j,hj⟩
    interval_cases j <;> exact h
  rw [PV_Src_Forest_AuxContent.note_digest]
  exact hd.trans (congrArg Result.ok he)

theorem transfer : CopyRecords.nullifier ⟨transferWitness,transferPublic⟩ =
    ok PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
  rw [CopyRecords.nullifier,transfer_raw]
  with_unfolding_all rfl

theorem withdrawal_raw :
    note_digest_r withdrawalWitness withdrawalPublic 26#usize =
      ok PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
  let W := PV_Src_Forest_PrimitiveArguments.wordWitness withdrawalWitness
  let P := PV_Src_Forest_PrimitiveArguments.wordPublic withdrawalPublic
  obtain ⟨d,hd,hl,hc⟩ := PV_RunJoin_NullifierLift16.nullifier W P (PV_RunJoin_FixtureRecords.base false)
    (by rfl) withdrawal_checked
  have sk : (toModel (K := M) W).sk = PV_RunJoin_FixtureRecords.digest 10 := by
    funext i; fin_cases i <;> rfl
  have salt : (toModel (K := M) W).salt = PV_RunJoin_FixtureRecords.digest 100 := by
    funext i; fin_cases i <;> rfl
  rw [sk,salt,PV_RunJoin_FixtureHashModel.nullifier] at hl
  have canonical : Canon8 PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
    intro j hj; interval_cases j <;> decide
  have he : d = PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    have bound : j < 8 := by simpa using hj
    apply PV_RunJoin_LeafLift16.word_injective (hc j hj) (canonical j bound)
    have h := hl ⟨j,hj⟩
    interval_cases j <;> exact h
  rw [PV_Src_Forest_AuxContent.note_digest]
  exact hd.trans (congrArg Result.ok he)

theorem withdrawal : CopyRecords.nullifier ⟨withdrawalWitness,withdrawalPublic⟩ =
    ok PV_RunJoin_RecordedTransfer.publicRecord.nullifier := by
  rw [CopyRecords.nullifier,withdrawal_raw]
  with_unfolding_all rfl

#print axioms transfer_raw
#print axioms transfer
#print axioms withdrawal_raw
#print axioms withdrawal
end R1Z.PV_RunJoin_Nullifier16
