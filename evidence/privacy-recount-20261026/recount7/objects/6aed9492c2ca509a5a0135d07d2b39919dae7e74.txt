import R1Z.PV_RunJoin_LeafLift16
import R1Z.PV_RunJoin_FixtureReturns16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_InputLeaf16
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M

theorem transfer_raw :
    input_leaf_r transferWitness transferPublic =
      ok PV_RunJoin_FixtureArguments.witness.pair.pair_leaf.first_commitment := by
  let W := PV_Src_Forest_PrimitiveArguments.wordWitness transferWitness
  let P := PV_Src_Forest_PrimitiveArguments.wordPublic transferPublic
  obtain ⟨d,hd,hl,hc⟩ := PV_RunJoin_LeafLift16.input W P (PV_RunJoin_FixtureRecords.base false)
    (by rfl) transfer_checked
  have sk : (toModel (K := M) W).sk = PV_RunJoin_FixtureRecords.digest 10 := by
    funext i; fin_cases i <;> rfl
  have salt : (toModel (K := M) W).salt = PV_RunJoin_FixtureRecords.digest 100 := by
    funext i; fin_cases i <;> rfl
  have value : (toModel (K := M) W).inputValue.val = 1000 := by rfl
  rw [sk,salt,value,show (PV_RunJoin_FixtureRecords.base false).assetId = 77 from rfl] at hl
  simp only [Nat.cast_ofNat] at hl
  rw [PV_RunJoin_FixtureHashModel.input_commitment] at hl
  have he : d = PV_RunJoin_FixtureArguments.witness.pair.pair_leaf.first_commitment := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    have bound : j < 8 := by simpa using hj
    apply PV_RunJoin_LeafLift16.word_injective (hc j hj) (PV_RunJoin_FixtureAdmission.first j hj)
    have h := hl ⟨j,hj⟩
    interval_cases j <;> exact h
  rw [PV_Src_Forest_AuxContent.input_digest]
  exact hd.trans (congrArg Result.ok he)

theorem transfer : CopyRecords.input_leaf ⟨transferWitness,transferPublic⟩ =
    ok PV_RunJoin_FixtureArguments.witness.pair.pair_leaf.first_commitment := by
  rw [CopyRecords.input_leaf,transfer_raw]
  with_unfolding_all rfl

theorem withdrawal_raw :
    input_leaf_r withdrawalWitness withdrawalPublic =
      ok PV_RunJoin_FixtureArguments.witness.pair.pair_leaf.first_commitment := by
  let W := PV_Src_Forest_PrimitiveArguments.wordWitness withdrawalWitness
  let P := PV_Src_Forest_PrimitiveArguments.wordPublic withdrawalPublic
  obtain ⟨d,hd,hl,hc⟩ := PV_RunJoin_LeafLift16.input W P (PV_RunJoin_FixtureRecords.base false)
    (by rfl) withdrawal_checked
  have sk : (toModel (K := M) W).sk = PV_RunJoin_FixtureRecords.digest 10 := by
    funext i; fin_cases i <;> rfl
  have salt : (toModel (K := M) W).salt = PV_RunJoin_FixtureRecords.digest 100 := by
    funext i; fin_cases i <;> rfl
  have value : (toModel (K := M) W).inputValue.val = 1000 := by rfl
  rw [sk,salt,value,show (PV_RunJoin_FixtureRecords.base false).assetId = 77 from rfl] at hl
  simp only [Nat.cast_ofNat] at hl
  rw [PV_RunJoin_FixtureHashModel.input_commitment] at hl
  have he : d = PV_RunJoin_FixtureArguments.witness.pair.pair_leaf.first_commitment := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    have bound : j < 8 := by simpa using hj
    apply PV_RunJoin_LeafLift16.word_injective (hc j hj) (PV_RunJoin_FixtureAdmission.first j hj)
    have h := hl ⟨j,hj⟩
    interval_cases j <;> exact h
  rw [PV_Src_Forest_AuxContent.input_digest]
  exact hd.trans (congrArg Result.ok he)

theorem withdrawal : CopyRecords.input_leaf ⟨withdrawalWitness,withdrawalPublic⟩ =
    ok PV_RunJoin_FixtureArguments.witness.pair.pair_leaf.first_commitment := by
  rw [CopyRecords.input_leaf,withdrawal_raw]
  with_unfolding_all rfl

#print axioms transfer_raw
#print axioms transfer
#print axioms withdrawal_raw
#print axioms withdrawal
end R1Z.PV_RunJoin_InputLeaf16
