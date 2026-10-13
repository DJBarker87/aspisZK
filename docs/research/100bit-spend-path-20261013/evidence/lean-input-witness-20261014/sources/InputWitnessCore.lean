import R1InputPairSelection

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

theorem trace_sibling (pub : Public K) (A : Trace K) (hb : CopyLinkBalance pub A) :
    (tracePath A 0).2 = if (tracePath A 0).1 then
      (InputPair.leaf A).firstCommitment else (InputPair.leaf A).secondCommitment := by
  classical
  rw [InputPairSelection.path_bit]
  by_cases hz : A 0 913 = 0
  · rw [if_pos hz]
    change (tracePath A 0).2 = (InputPair.leaf A).secondCommitment
    have hp : (tracePath A 0).2 = fun i : Fin 8 => A ⟨8 + i.val, by omega⟩ 914 := by
      unfold tracePath
      change ((if A 0 913 = 0 then _ else _) : Bool × R0P.Digest K).2 = _
      rw [if_pos hz]
      rfl
    rw [hp]
    funext i
    exact (InputPairSelection.right_path pub A hb i).symm
  · rw [if_neg hz]
    change (tracePath A 0).2 = (InputPair.leaf A).firstCommitment
    have hp : (tracePath A 0).2 = fun i : Fin 8 => A (i.castAdd 21) 914 := by
      unfold tracePath
      change ((if A 0 913 = 0 then _ else _) : Bool × R0P.Digest K).2 = _
      rw [if_neg hz]
      rfl
    rw [hp]
    funext i
    exact (InputPairSelection.left_path pub A hb i).symm

/-- The first membership step hashes this exact ordered valid pair. -/
theorem pair_head (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K)
    (h : Relation pub value sk salt path pair) :
    merkleStep (noteCommitment (ownerKey sk) value pub.assetId salt) (path 0).1 (path 0).2 =
      nodeCompress pair.firstCommitment pair.secondCommitment := by
  rw [← h.commitment, h.sibling]
  cases hb : (path 0).1 <;> simp only [PairLeaf.selectedCommitment, merkleStep,
    Bool.false_eq_true, if_false, if_true]

#print axioms trace_sibling
#print axioms pair_head
end AspisR1.InputWitnessCore
