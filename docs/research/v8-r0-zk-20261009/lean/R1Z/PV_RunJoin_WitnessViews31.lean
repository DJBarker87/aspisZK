import R1Z.PV_RunJoin_SemanticChange30
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_WitnessViews31
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap PV_Src_NativeInput
open PV_RunJoin_SemanticChange30
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem pair_first (i : Input) :
    (witness (K := K) i).pair.firstCommitment = digK i.witness.pair.pair_leaf.first_commitment := by
  change (BuilderSpendRelation.modelWitness (witness (K := K) i)).pairFirst = _
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  rfl
#print axioms pair_first

theorem pair_second (i : Input) :
    (witness (K := K) i).pair.secondCommitment = digK i.witness.pair.pair_leaf.second_commitment := by
  change (BuilderSpendRelation.modelWitness (witness (K := K) i)).pairSecond = _
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  rfl
#print axioms pair_second

theorem pair_occupied (i : Input) :
    (witness (K := K) i).pair.secondOccupied = liftU i.witness.pair.pair_leaf.second_occupied := by
  change (BuilderSpendRelation.modelWitness (witness (K := K) i)).pairOccupied = _
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  rfl
#print axioms pair_occupied

theorem pair_inverse (i : Input) :
    (witness (K := K) i).pair.secondOccupancyInverse = liftU i.witness.pair.pair_leaf.second_occupancy_inverse := by
  change (BuilderSpendRelation.modelWitness (witness (K := K) i)).pairInverse = _
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  rfl
#print axioms pair_inverse

theorem first_direction (i : Input) :
    ((witness (K := K) i).path 0).1 = i.witness.pair.selected_second := by
  change ((BuilderSpendRelation.modelWitness (witness (K := K) i)).path 0).1 = _
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  cases h : i.witness.pair.selected_second <;> simp only [toModel,bitB,PV_RunJoin_SemanticChange30.witness]
  all_goals rfl
#print axioms first_direction

theorem first_sibling (i : Input) :
    ((witness (K := K) i).path 0).2 =
      if i.witness.pair.selected_second then digK i.witness.pair.pair_leaf.first_commitment
      else digK i.witness.pair.pair_leaf.second_commitment := by
  change ((BuilderSpendRelation.modelWitness (witness (K := K) i)).path 0).2 = _
  unfold witness
  rw [BuilderFieldNormalization.decoded_witness]
  cases h : i.witness.pair.selected_second <;> rfl
#print axioms first_sibling
end R1Z.PV_RunJoin_WitnessViews31
