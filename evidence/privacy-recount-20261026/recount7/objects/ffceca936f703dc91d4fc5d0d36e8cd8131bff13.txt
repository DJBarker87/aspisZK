import R1Z.PV_RunJoin_TransferWitness20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WithdrawalWitness20
open R0Z.WriterRefine R0Z.BuilderModel PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
local notation "M" => PV_RunJoin_FixtureRecords.M
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

/-- Withdrawal's absent recipient is encoded by zero fields in the source record. -/
def witness : AspisR1.SpendRelation.Wspend :=
  { PV_RunJoin_FixtureRecords.witness true with
    recipientOwner := fun _ => 0, recipientSalt := fun _ => 0 }

theorem source : toModel (K := M) (wordWitness withdrawalWitness) =
    BuilderSpendRelation.modelWitness witness := by
  unfold toModel BuilderSpendRelation.modelWitness witness PV_RunJoin_FixtureRecords.witness
  congr 1
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · exact PV_RunJoin_FixturePathInputs16.withdrawal_path
  · change _ = R0P.noteCommitment _ _ _ _
    rw [PV_RunJoin_FixtureHashModel.input_commitment]
    funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
  · exact PV_RunJoin_TransferWitness20.inverse
  · funext i; fin_cases i <;> with_unfolding_all rfl
  · funext i; fin_cases i <;> with_unfolding_all rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl
#print axioms source

theorem admission : BuilderSpendRelation.RspendPlus (PV_RunJoin_FixtureRecords.fixturePublic true) witness := by
  exact PV_RunJoin_FixtureRecords.withdrawal_spendPlus
#print axioms admission
end R1Z.PV_RunJoin_WithdrawalWitness20
