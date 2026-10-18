import Mathlib.Tactic

/-!
# Algebraic occupancy for V7 Pool pair leaves

The Pool pair leaf never represents an empty slot by asking that a particular
digest have no preimage.  The first slot is occupied by construction.  The
second slot carries a field-valued occupancy bit and a zero-test witness for a
fixed sentinel limb of its commitment.  The constraints make occupancy zero
exactly when that sentinel is zero; an empty slot additionally forces every
commitment limb to zero.  Spending a selected slot separately requires its
occupancy value to equal one.

The pair-tree leaf is the ordinary lowest internal node of a depth-21 note
tree: its one-permutation compression input is the ordered pair of complete
eight-limb commitments.  Occupancy is not squeezed into an already-full hash
lane.  Instead it is a function of the fully committed second digest.  An
honest second output whose sentinel happens to be zero must resample its note
salt; this is a liveness rejection event, not an assumption that zero has no
preimage.  Collision resistance of Poseidon compression is deliberately
outside this algebraic file.
-/

set_option autoImplicit false

namespace AspisPool.V7PairLeafOccupancy

abbrev Digest (K : Type) := Fin 8 → K

/-- One transaction appends one pair.  Slot zero is always occupied; slot one
is present exactly when `secondOccupied = 1`. -/
structure PairLeaf (K : Type) where
  firstCommitment : Digest K
  secondOccupied : K
  secondCommitment : Digest K
  secondOccupancyInverse : K

/-- The last M31 limb is the fixed zero-test sentinel.  Any fixed limb would
work; pinning lane seven makes the encoding and source bridge unambiguous. -/
def PairLeaf.secondSentinel {K : Type} (leaf : PairLeaf K) : K :=
  leaf.secondCommitment ⟨7, by decide⟩

/-- Exact algebraic validity constraints for a pair leaf. -/
def PairLeaf.Valid {K : Type} [CommRing K] (leaf : PairLeaf K) : Prop :=
  leaf.secondOccupied * (leaf.secondOccupied - 1) = 0 ∧
    leaf.secondSentinel * leaf.secondOccupancyInverse =
      leaf.secondOccupied ∧
    (1 - leaf.secondOccupied) * leaf.secondOccupancyInverse = 0 ∧
    ∀ lane, (1 - leaf.secondOccupied) * leaf.secondCommitment lane = 0

/-- The occupancy value selected by a private membership witness. -/
def PairLeaf.selectedOccupied {K : Type} [OfNat K 1]
    (leaf : PairLeaf K) (secondSlot : Bool) : K :=
  if secondSlot then leaf.secondOccupied else 1

/-- The commitment selected by the same private side bit. -/
def PairLeaf.selectedCommitment {K : Type}
    (leaf : PairLeaf K) (secondSlot : Bool) : Digest K :=
  if secondSlot then leaf.secondCommitment else leaf.firstCommitment

/-- The relation-level spend gate.  Membership in the pair hash is not enough:
the privately selected slot must also be occupied. -/
def PairLeaf.SelectedSlotIsSpendable {K : Type} [OfNat K 1]
    (leaf : PairLeaf K) (secondSlot : Bool) : Prop :=
  leaf.selectedOccupied secondSlot = 1


end AspisPool.V7PairLeafOccupancy


set_option pp.universes true in
#check @AspisPool.V7PairLeafOccupancy.Digest

#print AspisPool.V7PairLeafOccupancy.Digest
#print axioms AspisPool.V7PairLeafOccupancy.Digest

#print AspisPool.V7PairLeafOccupancy.PairLeaf
#print axioms AspisPool.V7PairLeafOccupancy.PairLeaf

#print AspisPool.V7PairLeafOccupancy.PairLeaf.secondSentinel
#print axioms AspisPool.V7PairLeafOccupancy.PairLeaf.secondSentinel

#print AspisPool.V7PairLeafOccupancy.PairLeaf.Valid
#print axioms AspisPool.V7PairLeafOccupancy.PairLeaf.Valid

#print AspisPool.V7PairLeafOccupancy.PairLeaf.selectedOccupied
#print axioms AspisPool.V7PairLeafOccupancy.PairLeaf.selectedOccupied

#print AspisPool.V7PairLeafOccupancy.PairLeaf.selectedCommitment
#print axioms AspisPool.V7PairLeafOccupancy.PairLeaf.selectedCommitment

#print AspisPool.V7PairLeafOccupancy.PairLeaf.SelectedSlotIsSpendable
#print axioms AspisPool.V7PairLeafOccupancy.PairLeaf.SelectedSlotIsSpendable
