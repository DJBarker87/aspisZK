import R1InputWitnessCore

/-! Executable decision procedure for exactly `InputWitnessCore.Relation`.
This is a generic checker for the abstract field model; it makes no concrete
Rust/source correspondence claim. -/
set_option autoImplicit false
namespace AspisR1.InputWitnessCheck

open R0P AspisPool.V7PairLeafOccupancy

variable {K : Type} [Field K] [DecidableEq K]

/-- Executable universal check over the eight digest lanes. -/
def allFin8 (p : Fin 8 → Bool) : Bool := (List.ofFn p).all id

theorem allFin8_eq_true_iff (p : Fin 8 → Bool) :
    allFin8 p = true ↔ ∀ i, p i = true := by
  change (List.ofFn p).all id = true ↔ ∀ i, p i = true
  rw [List.all_eq_true]
  constructor
  · intro h i
    simpa using h (p i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simpa using h i

/-- Equality of two eight-limb digests by eight pointwise equality checks. -/
def digestEqCheck (left right : R0P.Digest K) : Bool :=
  allFin8 (fun lane => decide (left lane = right lane))

theorem digestEqCheck_eq_true_iff (left right : R0P.Digest K) :
    digestEqCheck left right = true ↔ left = right := by
  rw [digestEqCheck, allFin8_eq_true_iff]
  constructor
  · intro h
    funext lane
    exact of_decide_eq_true (h lane)
  · intro h lane
    exact decide_eq_true (congrFun h lane)

/-- The four finite checks spelling out `PairLeaf.Valid`. -/
def pairValidCheck (pair : PairLeaf K) : Bool :=
  decide (pair.secondOccupied * (pair.secondOccupied - 1) = 0) &&
    decide (pair.secondSentinel * pair.secondOccupancyInverse = pair.secondOccupied) &&
    decide ((1 - pair.secondOccupied) * pair.secondOccupancyInverse = 0) &&
    allFin8 (fun lane =>
      decide ((1 - pair.secondOccupied) * pair.secondCommitment lane = 0))

theorem pairValidCheck_eq_true_iff (pair : PairLeaf K) :
    pairValidCheck pair = true ↔ pair.Valid := by
  simp [pairValidCheck, PairLeaf.Valid, PairLeaf.secondSentinel,
    allFin8_eq_true_iff]

/-- Bool checker expanding all six fields of `InputWitnessCore.Relation`. -/
def check (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K) : Bool :=
  pairValidCheck pair &&
    decide (pair.selectedOccupied (path 0).1 = 1) &&
    digestEqCheck (pair.selectedCommitment (path 0).1)
      (noteCommitment (ownerKey sk) value pub.assetId salt) &&
    digestEqCheck (path 0).2
      (if (path 0).1 then pair.firstCommitment else pair.secondCommitment) &&
    digestEqCheck pub.nullifier (nullifierHash sk salt) &&
    digestEqCheck pub.anchor
      (merkleRoot (noteCommitment (ownerKey sk) value pub.assetId salt) path)

theorem check_eq_true_iff (pub : Public K) (value : K) (sk salt : R0P.Digest K)
    (path : Fin 24 → Bool × R0P.Digest K) (pair : PairLeaf K) :
    check pub value sk salt path pair = true ↔
      InputWitnessCore.Relation pub value sk salt path pair := by
  constructor
  · intro h
    simp only [check, Bool.and_eq_true, pairValidCheck_eq_true_iff,
      digestEqCheck_eq_true_iff, decide_eq_true_eq] at h
    rcases h with ⟨hvalid, hspend, hcommitment, hsibling, hnullifier, hmembership⟩
    exact ⟨hvalid, hspend, hcommitment, hsibling, hnullifier, hmembership⟩
  · intro h
    simp only [check, Bool.and_eq_true, pairValidCheck_eq_true_iff,
      digestEqCheck_eq_true_iff, decide_eq_true_eq]
    exact ⟨h.valid, h.spendable, h.commitment, h.sibling, h.nullifier, h.membership⟩

#print axioms allFin8_eq_true_iff
#print axioms digestEqCheck_eq_true_iff
#print axioms pairValidCheck_eq_true_iff
#print axioms check_eq_true_iff

end AspisR1.InputWitnessCheck
