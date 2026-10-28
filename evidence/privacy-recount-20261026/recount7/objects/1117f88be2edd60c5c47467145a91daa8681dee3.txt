import R1Z.PV_RunJoin_CanonicalPublic21
import R1Z.PV_RunJoin_CanonicalFixtures
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeFibre21
local notation "K" => PrivacyR1AcctBasis.K
local instance : CharP K 2147483647 :=
  charP_of_injective_algebraMap (algebraMap (ZMod AspisCircleGroupOrder.P) K).injective AspisCircleGroupOrder.P

theorem transfer_source : BuilderPublicProjection.semanticPublic
    (PV_Src_Public.output PV_RunJoin_RecordedTransfer.publicInput) =
    PV_RunJoin_FixtureRecords.fixturePublic false :=
  (PV_Src_Public.public_eq _).trans PV_RunJoin_CanonicalPublic21.transfer
#print axioms transfer_source

theorem withdrawal_source : BuilderPublicProjection.semanticPublic
    (PV_Src_Public.output PV_RunJoin_RecordedWithdrawal.publicInput) =
    PV_RunJoin_FixtureRecords.fixturePublic true :=
  (PV_Src_Public.public_eq _).trans PV_RunJoin_CanonicalPublic21.withdrawal
#print axioms withdrawal_source

/-- The actual recorded native public projection has a canonical witness.
No selected Input, byte decoder, runtime or environmental P law is inferred. -/
theorem transfer : ∃ w : (BuilderSource.prover («K» := K)).Instance,
    (BuilderSource.prover («K» := K)).public w =
      R1J.SpendWitnessMap.mapPub (PV_Src_Public.canonicalPublic PV_RunJoin_RecordedTransfer.publicInput) := by
  rw [PV_RunJoin_CanonicalPublic21.transfer]
  exact ⟨PV_RunJoin_CanonicalFixtures.transfer,PV_RunJoin_CanonicalFixtures.transfer_public⟩
#print axioms transfer

theorem withdrawal : ∃ w : (BuilderSource.prover («K» := K)).Instance,
    (BuilderSource.prover («K» := K)).public w =
      R1J.SpendWitnessMap.mapPub (PV_Src_Public.canonicalPublic PV_RunJoin_RecordedWithdrawal.publicInput) := by
  rw [PV_RunJoin_CanonicalPublic21.withdrawal]
  exact ⟨PV_RunJoin_CanonicalFixtures.withdrawal,PV_RunJoin_CanonicalFixtures.withdrawal_public⟩
#print axioms withdrawal
end R1Z.PV_RunJoin_NativeFibre21

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeAdmitted21
open R0Z.WriterRefine
local notation "M" => PV_RunJoin_FixtureRecords.M
/-- Admission and trace at the recorded native public, for the original returned payload. -/
theorem transfer : ∃ w : AspisR1.SpendRelation.Wspend,
    BuilderSpendRelation.RspendPlus (PV_Src_Public.canonicalPublic PV_RunJoin_RecordedTransfer.publicInput) w ∧
    ∀ c r, liftU (K := M) (PV_Src_Forest_Columns.read PV_RunJoin_TransferPayload20.output.semantic_c1.c1 c r) =
      R0Z.BuilderModel.buildModel (PV_Src_Public.canonicalPublic PV_RunJoin_RecordedTransfer.publicInput)
        (BuilderSpendRelation.modelWitness w) c r := by
  rw [PV_RunJoin_CanonicalPublic21.transfer]
  exact PV_RunJoin_AdmittedPayload20.transfer
#print axioms transfer

theorem withdrawal : ∃ w : AspisR1.SpendRelation.Wspend,
    BuilderSpendRelation.RspendPlus (PV_Src_Public.canonicalPublic PV_RunJoin_RecordedWithdrawal.publicInput) w ∧
    ∀ c r, liftU (K := M) (PV_Src_Forest_Columns.read PV_RunJoin_WithdrawalPayload20.output.semantic_c1.c1 c r) =
      R0Z.BuilderModel.buildModel (PV_Src_Public.canonicalPublic PV_RunJoin_RecordedWithdrawal.publicInput)
        (BuilderSpendRelation.modelWitness w) c r := by
  rw [PV_RunJoin_CanonicalPublic21.withdrawal]
  exact PV_RunJoin_AdmittedPayload20.withdrawal
#print axioms withdrawal
end R1Z.PV_RunJoin_NativeAdmitted21
