import R1PairLeafOccupancyCore
import R0P.Semantics

/-! One input relation with ownership, nullifier, occupied pair selection,
and a 24-level membership path. The pair's other commitment is the first
path sibling, so pair validity cannot be attached to an unrelated pair. -/
set_option autoImplicit false
namespace AspisR1.InputWitnessCore
open R0P AspisPool.V7PairLeafOccupancy
variable {K : Type} [Field K]

attribute [local irreducible] nodeCompress poseidonPermutation

structure Relation (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K) : Prop where
  valid : pair.Valid
  spendable : pair.SelectedSlotIsSpendable (path 0).1
  commitment : pair.selectedCommitment (path 0).1 =
    noteCommitment (ownerKey sk) value pub.assetId salt
  sibling : (path 0).2 = if (path 0).1 then pair.firstCommitment else pair.secondCommitment
  nullifier : pub.nullifier = nullifierHash sk salt
  membership : pub.anchor =
    merkleRoot (noteCommitment (ownerKey sk) value pub.assetId salt) path

end AspisR1.InputWitnessCore


set_option pp.universes true in
#check @AspisR1.InputWitnessCore.Relation

#print AspisR1.InputWitnessCore.Relation
#print axioms AspisR1.InputWitnessCore.Relation
