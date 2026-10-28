import R1Z.PV_RunJoin_FixtureInputCommitment
import R1Z.PV_RunJoin_FixtureNullifier
import R1Z.PV_RunJoin_FixtureArguments

/-! Literal/field association for input commitment and nullifier. This is
mathematical fixture data and does not identify the shipped mapper or parser. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_FixtureLiteralFacts
open Aeneas Aeneas.Std R0Z.WriterRefine R0P
open PV_RunJoin_FixtureHashModel PV_RunJoin_FixtureRecords

theorem input_commitment :
    (fun i : Fin 8 => liftU (K := Scalar)
      PV_RunJoin_FixtureArguments.witness.pair.pair_leaf.first_commitment.val[i.val]!) =
      noteCommitment (ownerKey (digest 10)) 1000 77 (digest 100) := by
  rw [PV_RunJoin_FixtureHashModel.input_commitment]
  funext i
  fin_cases i <;> rfl

theorem transfer_nullifier :
    (fun i : Fin 8 => liftU (K := Scalar) PV_RunJoin_RecordedTransfer.publicRecord.nullifier.val[i.val]!) =
      nullifierHash (digest 10) (digest 100) := by
  rw [PV_RunJoin_FixtureHashModel.nullifier]
  funext i
  fin_cases i <;> rfl

theorem withdrawal_nullifier :
    (fun i : Fin 8 => liftU (K := Scalar) PV_RunJoin_RecordedWithdrawal.publicRecord.nullifier.val[i.val]!) =
      nullifierHash (digest 10) (digest 100) := by
  rw [PV_RunJoin_FixtureHashModel.nullifier]
  funext i
  fin_cases i <;> rfl

#print axioms input_commitment
#print axioms transfer_nullifier
#print axioms withdrawal_nullifier
end R1Z.PV_RunJoin_FixtureLiteralFacts
