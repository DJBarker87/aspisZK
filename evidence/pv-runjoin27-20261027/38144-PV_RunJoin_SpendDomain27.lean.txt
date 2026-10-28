import R1Z.PV_RunJoin_FixtureRecords
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SpendDomain27
open R0P AspisR1 AspisR1.SpendRelation
open PV_RunJoin_FixtureRecords
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

/-- Full withdrawal of the existing 1000-unit input. All change metadata is
canonical mathematical M31 data; change value is zero. -/
def witness : Wspend :=
  { PV_RunJoin_FixtureRecords.witness true with
    outputValue := ⟨1000, by decide⟩, changeValue := ⟨0, by decide⟩ }

def base : Public M :=
  { PV_RunJoin_FixtureRecords.base true with
    change := noteCommitment witness.changeOwner 0 77 witness.changeSalt
    withdrawalAmount := some 1000 }

def statement : Public M := attachAppend base (nodeCompress base.change (fun _ => 0))

theorem input_relation : InputWitnessCore.Relation statement witness.inputValue.val
    witness.sk witness.salt witness.path witness.pair where
  valid := pair_valid
  spendable := rfl
  commitment := rfl
  sibling := rfl
  nullifier := rfl
  membership := rfl
#print axioms input_relation

theorem append : AppendBinding statement :=
  seal_append base _ rfl
#print axioms append

theorem admitted : BuilderSpendRelation.RspendPlus statement witness := by
  refine ⟨⟨?_,input_relation,?_,rfl,rfl,append⟩,?_⟩
  · refine ⟨rfl,rfl,?_⟩
    change (some (1000 : M)) ≠ some 0
    intro h
    have e := congrArg (fun x : M => x.val) (Option.some.inj h)
    change 1000 = 0 at e
    omega
  · decide
  · intro impossible
    cases impossible
#print axioms admitted

theorem change_zero : witness.changeValue.val = 0 := rfl
#print axioms change_zero

theorem positive_change_does_not_follow :
    ¬ (∀ p : Public M, ∀ w : Wspend,
      BuilderSpendRelation.RspendPlus p w → 0 < w.changeValue.val) := by
  intro h
  have impossible := h statement witness admitted
  change 0 < 0 at impossible
  omega
#print axioms positive_change_does_not_follow

/-- Any encoding which preserves the admitted value still has zero change.
In particular, requiring positive change cannot be a faithful representation
choice for the complete admitted relation. -/
theorem every_value_preserving_encoding_zero (v : Nat)
    (preserves : v = witness.changeValue.val) : v = 0 := preserves
#print axioms every_value_preserving_encoding_zero
end R1Z.PV_RunJoin_SpendDomain27
