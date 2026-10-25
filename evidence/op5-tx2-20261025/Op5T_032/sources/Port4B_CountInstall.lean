import Port4B_SortInstall

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_CountInstall
open Aeneas Aeneas.Std Result
open OraclePortFrozenOrder
attribute [local instance] Classical.propDecidable

def countValue (is : List Nat) (well : wellFormed is) : Usize :=
  UScalar.ofNat (MultiproofConeCountLevels.sourceCount 18 is) (by
    have bound := MultiproofConeCountBounds.eighteen_bound is well.2.1 well.2.2.1
    scalar_tac)

/-- Named P6 count lowering: the validated binary recurrence, with no oracle
effects. The in-place group/height projection is independently kernel proved. -/
def nodeCount (arity : Port3_NativeBatchBody.multiproof.Arity) (is : Slice U32) : Result (Option Usize) :=
  match arity with
  | .Two => if well : wellFormed (is.val.map UScalar.val)
    then ok (some (countValue _ well)) else ok none
  | .Eight => fail .panic

def install (base : Port3_NativeBatchBody.Ops) : Port3_NativeBatchBody.Ops :=
  {Port4B_SortInstall.install base with op11:=nodeCount}

theorem accepted_count (front : Slice U32) (count : Usize)
    (accepted : nodeCount .Two front=ok (some count)) :
    wellFormed (front.val.map UScalar.val) ∧
    count.val=OraclePortFrozenOrder.nodeCount 18 (front.val.map UScalar.val) ∧ count.val≤288 := by
  simp only [nodeCount] at accepted
  split at accepted
  next well =>
    have same := Option.some.inj (Result.ok.inj accepted)
    subst count
    refine ⟨well,?_,MultiproofConeCountBounds.eighteen_bound _ well.2.1 well.2.2.1⟩
    exact MultiproofConeCountLevels.count_eq _ _ well.2.2.1
  next bad => cases accepted

#print axioms accepted_count
end AspisR1.Port4B_CountInstall
end
