import R1InputWitnessCore

/-! Executable decision procedure for exactly `InputWitnessCore.Relation`.
This is a generic checker for the abstract field model; it makes no concrete
Rust/source correspondence claim. -/
set_option autoImplicit false
namespace AspisR1.InputWitnessCheck

open R0P AspisPool.V7PairLeafOccupancy

variable {K : Type} [Field K] [DecidableEq K]

def pairValidSpec (pair : PairLeaf K) : Prop :=
  (pair.secondOccupied * (pair.secondOccupied - 1) = 0 ∧
    pair.secondSentinel * pair.secondOccupancyInverse = pair.secondOccupied) ∧
    ((1 - pair.secondOccupied) * pair.secondOccupancyInverse = 0 ∧
      ∀ lane : Fin 8, (1 - pair.secondOccupied) * pair.secondCommitment lane = 0)

def checkSpec (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K) : Prop :=
  pairValidSpec pair ∧
    ((pair.selectedOccupied (path 0).1 = 1 ∧
      pair.selectedCommitment (path 0).1 =
        noteCommitment (ownerKey sk) value pub.assetId salt) ∧
      ((path 0).2 =
        if (path 0).1 then pair.firstCommitment else pair.secondCommitment) ∧
      (pub.nullifier = nullifierHash sk salt ∧
        pub.anchor =
          merkleRoot (noteCommitment (ownerKey sk) value pub.assetId salt) path))

def check (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K) : Bool :=
  decide (checkSpec pub value sk salt path pair)

theorem checkSpec_iff_relation (pub : Public K) (value : K)
    (sk salt : R0P.Digest K) (path : Fin 24 → Bool × R0P.Digest K)
    (pair : PairLeaf K) :
    checkSpec pub value sk salt path pair ↔
      InputWitnessCore.Relation pub value sk salt path pair := by
  constructor
  · rintro ⟨⟨⟨hvalid₁, hvalid₂⟩, ⟨hvalid₃, hvalid₄⟩⟩,
      ⟨hspend, hcommit⟩, hsibling, ⟨hnullifier, hmembership⟩⟩
    exact ⟨⟨hvalid₁, hvalid₂, hvalid₃, hvalid₄⟩, hspend, hcommit,
      hsibling, hnullifier, hmembership⟩
  · intro h
    exact ⟨⟨⟨h.valid.1, h.valid.2.1⟩, ⟨h.valid.2.2.1, h.valid.2.2.2⟩⟩,
      ⟨h.spendable, h.commitment⟩, h.sibling, ⟨h.nullifier, h.membership⟩⟩

theorem check_eq_true_iff (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K) :
    check pub value sk salt path pair = true ↔
      InputWitnessCore.Relation pub value sk salt path pair := by
  simp [check, checkSpec_iff_relation]

#print axioms checkSpec_iff_relation
#print axioms check_eq_true_iff

end AspisR1.InputWitnessCheck
