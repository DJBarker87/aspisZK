import R1Z.PV_RunJoin_PairValidity28
import R1Z.PV_RunJoin_TransferSentinel
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ZeroRecipient28
open R0P AspisR1 AspisR1.SpendRelation AspisPool.V7PairLeafOccupancy
open PV_RunJoin_FixtureRecords
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

/-- Preserve the checked 400-unit change commitment/sentinel, spending a
400-unit input into a zero-unit recipient and 400-unit change. -/
def pair : PairLeaf M := { PV_RunJoin_FixtureRecords.pair with
  firstCommitment := noteCommitment (ownerKey (digest 10)) 400 77 (digest 100) }
def witness : Wspend := { PV_RunJoin_FixtureRecords.witness false with
  inputValue := ⟨400, by decide⟩, outputValue := ⟨0, by decide⟩, pair := pair }
def base : Public M := { PV_RunJoin_FixtureRecords.base false with
  anchor := merkleRoot (noteCommitment (ownerKey (digest 10)) 400 77 (digest 100)) path
  recipient := some (noteCommitment (digest 300) 0 77 (digest 400)) }
def statement : Public M := attachAppend base
  (nodeCompress (noteCommitment (digest 300) 0 77 (digest 400)) base.change)

theorem valid : pair.Valid :=
  PV_RunJoin_PairValidity28.replace_first PV_RunJoin_FixtureRecords.pair
    (noteCommitment (ownerKey (digest 10)) 400 77 (digest 100)) pair_valid
#print axioms valid

theorem input_relation : InputWitnessCore.Relation statement witness.inputValue.val
    witness.sk witness.salt witness.path witness.pair where
  valid := valid
  spendable := rfl
  commitment := rfl
  sibling := rfl
  nullifier := rfl
  membership := rfl
#print axioms input_relation

theorem append : AppendBinding statement := seal_append base _ rfl
#print axioms append

theorem admitted : BuilderSpendRelation.RspendPlus statement witness := by
  refine ⟨⟨⟨rfl,rfl⟩,input_relation,?_,rfl,rfl,append⟩,?_⟩
  · decide
  · intro _
    exact PV_RunJoin_TransferSentinel.nonzero
#print axioms admitted

theorem positive_change : 0 < witness.changeValue.val := by decide
#print axioms positive_change

theorem zero_recipient : witness.outputValue.val = 0 := rfl
#print axioms zero_recipient

/-- Positivity of change alone cannot describe the transfer preparation
subset of the admitted relation. This is a semantic domain fact, not an
execution theorem for the native outer wrapper. -/
theorem admitted_positive_change_not_positive_recipient :
    ¬ (∀ p : Public M, ∀ w : Wspend, BuilderSpendRelation.RspendPlus p w →
      0 < w.changeValue.val → 0 < w.outputValue.val) := by
  intro h
  have bad := h statement witness admitted positive_change
  change 0 < 0 at bad
  omega
#print axioms admitted_positive_change_not_positive_recipient
end R1Z.PV_RunJoin_ZeroRecipient28
