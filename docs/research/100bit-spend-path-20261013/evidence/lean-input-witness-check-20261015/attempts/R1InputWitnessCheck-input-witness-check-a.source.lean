import R1InputWitnessCore

/-! Executable decision procedure for exactly `InputWitnessCore.Relation`.
This is a generic checker for the abstract field model; it makes no concrete
Rust/source correspondence claim. -/
set_option autoImplicit false
namespace AspisR1.InputWitnessCheck

open R0P AspisPool.V7PairLeafOccupancy

variable {K : Type} [Field K] [DecidableEq K]

def pairValidCheck (pair : PairLeaf K) : Bool :=
  decide (pair.secondOccupied * (pair.secondOccupied - 1) = 0) &&
    decide (pair.secondSentinel * pair.secondOccupancyInverse = pair.secondOccupied) &&
    decide ((1 - pair.secondOccupied) * pair.secondOccupancyInverse = 0) &&
    decide (∀ lane : Fin 8, (1 - pair.secondOccupied) * pair.secondCommitment lane = 0)

def check (pub : Public K) (value : K) (sk salt : Digest K)
    (path : Fin 24 → Bool × Digest K) (pair : PairLeaf K) : Bool :=
  pairValidCheck pair &&
    decide (pair.selectedOccupied (path 0).1 = 1) &&
    decide (pair.selectedCommitment (path 0).1 =
      noteCommitment (ownerKey sk) value pub.assetId salt) &&
    decide ((path 0).2 =
      if (path 0).1 then pair.firstCommitment else pair.secondCommitment) &&
    decide (pub.nullifier = nullifierHash sk salt) &&
    decide (pub.anchor =
      merkleRoot (noteCommitment (ownerKey sk) value pub.assetId salt) path)

theorem check_eq_true_iff (pub : Public K) (value : K) (sk salt : Digest K)
    (path : Fin 24 → Bool × Digest K) (pair : PairLeaf K) :
    check pub value sk salt path pair = true ↔
      InputWitnessCore.Relation pub value sk salt path pair := by
  simp [check, pairValidCheck, InputWitnessCore.Relation,
    PairLeaf.Valid, PairLeaf.SelectedSlotIsSpendable,
    PairLeaf.selectedOccupied, PairLeaf.selectedCommitment]

#print axioms check_eq_true_iff

end AspisR1.InputWitnessCheck
