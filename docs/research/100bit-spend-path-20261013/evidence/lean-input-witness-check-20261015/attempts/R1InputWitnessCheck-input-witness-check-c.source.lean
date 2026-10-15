import R1InputWitnessCore

/-! Executable decision procedure for exactly `InputWitnessCore.Relation`.
This is a generic checker for the abstract field model; it makes no concrete
Rust/source correspondence claim. -/
set_option autoImplicit false
namespace AspisR1.InputWitnessCheck

open R0P AspisPool.V7PairLeafOccupancy

variable {K : Type} [Field K] [DecidableEq K]

def digestEqCheck (left right : R0P.Digest K) : Bool :=
  Finset.univ.all (fun lane : Fin 8 => decide (left lane = right lane))

theorem digestEqCheck_eq_true_iff (left right : R0P.Digest K) :
    digestEqCheck left right = true ↔ left = right := by
  simp only [digestEqCheck, Finset.all_eq_true, Finset.mem_univ, true_and,
    decide_eq_true_eq]
  constructor
  · intro h
    funext lane
    exact h lane
  · intro h lane
    exact congrFun h lane

def pairValidCheck (pair : PairLeaf K) : Bool :=
  decide (pair.secondOccupied * (pair.secondOccupied - 1) = 0) &&
    decide (pair.secondSentinel * pair.secondOccupancyInverse = pair.secondOccupied) &&
    decide ((1 - pair.secondOccupied) * pair.secondOccupancyInverse = 0) &&
    Finset.univ.all (fun lane : Fin 8 =>
      decide ((1 - pair.secondOccupied) * pair.secondCommitment lane = 0))

theorem pairValidCheck_eq_true_iff (pair : PairLeaf K) :
    pairValidCheck pair = true ↔ pair.Valid := by
  simp [pairValidCheck, PairLeaf.Valid, PairLeaf.secondSentinel,
    Finset.all_eq_true]

def check (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K) : Bool :=
  pairValidCheck pair &&
    (decide (pair.selectedOccupied (path 0).1 = 1) &&
      (digestEqCheck (pair.selectedCommitment (path 0).1)
          (noteCommitment (ownerKey sk) value pub.assetId salt) &&
        (digestEqCheck (path 0).2
            (if (path 0).1 then pair.firstCommitment else pair.secondCommitment) &&
          (digestEqCheck pub.nullifier (nullifierHash sk salt) &&
            digestEqCheck pub.anchor
              (merkleRoot (noteCommitment (ownerKey sk) value pub.assetId salt) path))))

theorem check_eq_true_iff (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K) :
    check pub value sk salt path pair = true ↔
      InputWitnessCore.Relation pub value sk salt path pair := by
  simp only [check, Bool.and_eq_true, pairValidCheck_eq_true_iff,
    digestEqCheck_eq_true_iff, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with ⟨hvalid, hrest⟩
    rcases hrest with ⟨hspend, hrest⟩
    rcases hrest with ⟨hcommitment, hrest⟩
    rcases hrest with ⟨hsibling, hrest⟩
    rcases hrest with ⟨hnullifier, hmembership⟩
    exact ⟨hvalid, hspend, hcommitment, hsibling, hnullifier, hmembership⟩
  · intro h
    exact ⟨h.valid, h.spendable, h.commitment, h.sibling, h.nullifier, h.membership⟩

#print axioms digestEqCheck_eq_true_iff
#print axioms pairValidCheck_eq_true_iff
#print axioms check_eq_true_iff

end AspisR1.InputWitnessCheck
