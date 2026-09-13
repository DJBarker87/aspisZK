import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Finite ideal-salt counting

The external `coordinateFiberCap` premise is the precise finite form of
salt-obliviousness: after fixing every other salt and all allowed auxiliary
history, at most `q` values of the still-hidden coordinate trigger the probe
event. It is not a bound on the final bad-event mass.
-/
set_option autoImplicit false
namespace AspisV8PairedCommitment

noncomputable section
variable {Slot Salt PairIndex : Type*}
  [Fintype Slot] [DecidableEq Slot]
  [Fintype Salt] [DecidableEq Salt] [Nonempty Salt]

local instance finiteSubtypeOfFintype {α : Type*} [Fintype α]
    {predicate : α → Prop} : Finite {value : α // predicate value} :=
  Finite.of_injective (fun value => value.1)
    (fun _ _ equal => Subtype.ext equal)

abbrev SaltVector (Slot Salt : Type*) := Slot → Salt
abbrev OmitCoordinate (i : Slot) := {j : Slot // j ≠ i} → Salt

def rebuildCoordinate (i : Slot) (head : Salt) (tail : OmitCoordinate (Salt := Salt) i) :
    SaltVector Slot Salt :=
  fun j => if same : j = i then head else tail ⟨j, same⟩

def splitCoordinate (i : Slot) :
    SaltVector Slot Salt ≃ Salt × OmitCoordinate (Salt := Salt) i where
  toFun salts := (salts i, fun j => salts j)
  invFun pair := rebuildCoordinate i pair.1 pair.2
  left_inv salts := by
    funext j
    by_cases same : j = i
    · subst j
      simp [rebuildCoordinate]
    · simp [rebuildCoordinate, same]
  right_inv pair := by
    apply Prod.ext
    · simp [rebuildCoordinate]
    · funext j
      simp [rebuildCoordinate, j.property]

def coordinateFiber (probe : Slot → SaltVector Slot Salt → Prop)
    (i : Slot) (tail : OmitCoordinate (Salt := Salt) i) :=
  {head : Salt // probe i (rebuildCoordinate i head tail)}

def coordinateEventEquiv
    (probe : Slot → SaltVector Slot Salt → Prop) (i : Slot) :
    {salts : SaltVector Slot Salt // probe i salts} ≃
      Σ tail : OmitCoordinate (Salt := Salt) i, coordinateFiber probe i tail :=
  let splitTailFirst :=
    (splitCoordinate (Salt := Salt) i).trans
      (Equiv.prodComm Salt (OmitCoordinate (Salt := Salt) i))
  (splitTailFirst.subtypeEquiv fun salts => by
      have rebuilt :
          rebuildCoordinate i (salts i) (fun j => salts j) = salts :=
        (splitCoordinate (Salt := Salt) i).symm_apply_apply salts
      change probe i salts ↔
        probe i (rebuildCoordinate i (salts i) (fun j => salts j))
      rw [rebuilt]).trans
    (Equiv.subtypeProdEquivSigmaSubtype fun tail head =>
      probe i (rebuildCoordinate i head tail))

theorem omit_coordinate_card (i : Slot) :
    Fintype.card (OmitCoordinate (Salt := Salt) i) =
      Fintype.card Salt ^ (Fintype.card Slot - 1) := by
  rw [Fintype.card_fun]
  congr 1
  classical
  rw [Fintype.card_subtype_compl (fun j : Slot => j = i)]
  simp

theorem coordinate_event_count_le
    (probe : Slot → SaltVector Slot Salt → Prop) (q : Nat)
    (i : Slot)
    (fiberCap : ∀ tail, Nat.card (coordinateFiber probe i tail) ≤ q) :
    Nat.card {salts : SaltVector Slot Salt // probe i salts} ≤
      q * Fintype.card Salt ^ (Fintype.card Slot - 1) := by
  letI : ∀ tail : OmitCoordinate (Salt := Salt) i,
      Finite (coordinateFiber probe i tail) := fun _ =>
    Finite.of_injective (fun value => value.1)
      (fun _ _ equal => Subtype.ext equal)
  rw [Nat.card_congr (coordinateEventEquiv probe i), Nat.card_sigma]
  calc
    (∑ tail : OmitCoordinate (Salt := Salt) i,
        Nat.card (coordinateFiber probe i tail)) ≤
        ∑ _tail : OmitCoordinate (Salt := Salt) i, q := by
      exact Finset.sum_le_sum fun tail _ => fiberCap tail
    _ = q * Fintype.card Salt ^ (Fintype.card Slot - 1) := by
      simp [omit_coordinate_card, Nat.mul_comm]

def chooseIndexedEvent
    (probe : Slot → SaltVector Slot Salt → Prop) :
    {salts : SaltVector Slot Salt // ∃ i, probe i salts} →
      Σ i : Slot, {salts : SaltVector Slot Salt // probe i salts} :=
  fun salts =>
    let i := Classical.choose salts.2
    ⟨i, ⟨salts.1, Classical.choose_spec salts.2⟩⟩

theorem chooseIndexedEvent_injective
    (probe : Slot → SaltVector Slot Salt → Prop) :
    Function.Injective (chooseIndexedEvent probe) := by
  intro left right equal
  apply Subtype.ext
  exact congrArg (fun item : Σ i : Slot,
    {salts : SaltVector Slot Salt // probe i salts} => item.2.1) equal

/-- Adaptive probe union bound derived from coordinate-wise
salt-obliviousness, not assumed as a final bad-mass inequality. -/
theorem adaptive_probe_count_le
    (probe : Slot → SaltVector Slot Salt → Prop) (q : Nat)
    (fiberCap : ∀ i tail, Nat.card (coordinateFiber probe i tail) ≤ q) :
    Nat.card {salts : SaltVector Slot Salt // ∃ i, probe i salts} ≤
      Fintype.card Slot * q *
        Fintype.card Salt ^ (Fintype.card Slot - 1) := by
  letI : ∀ i : Slot, Finite {salts : SaltVector Slot Salt // probe i salts} :=
    fun _ => Finite.of_injective (fun salts => salts.1)
      (fun _ _ equal => Subtype.ext equal)
  letI : Finite (Σ i : Slot,
      {salts : SaltVector Slot Salt // probe i salts}) :=
    Finite.of_injective (fun item => (item.1, item.2.1)) (by
      intro left right equal
      rcases left with ⟨leftIndex, leftSalts⟩
      rcases right with ⟨rightIndex, rightSalts⟩
      simp only [Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, saltsEqual⟩
      have : leftSalts = rightSalts := Subtype.ext saltsEqual
      cases this
      rfl)
  calc
    Nat.card {salts : SaltVector Slot Salt // ∃ i, probe i salts} ≤
        Nat.card (Σ i : Slot,
          {salts : SaltVector Slot Salt // probe i salts}) :=
      Nat.card_le_card_of_injective (chooseIndexedEvent probe)
        (chooseIndexedEvent_injective probe)
    _ = ∑ i : Slot,
          Nat.card {salts : SaltVector Slot Salt // probe i salts} := by
      rw [Nat.card_sigma]
    _ ≤ ∑ _i : Slot,
          q * Fintype.card Salt ^ (Fintype.card Slot - 1) := by
      exact Finset.sum_le_sum fun i _ =>
        coordinate_event_count_le probe q i (fiberCap i)
    _ = Fintype.card Slot * q *
          Fintype.card Salt ^ (Fintype.card Slot - 1) := by
      simp [Nat.mul_assoc]

section Collision

variable [Fintype PairIndex]
  (pairLeft pairRight : PairIndex → Slot)
  (pairDistinct : ∀ pair, pairLeft pair ≠ pairRight pair)

def collisionAt (pair : PairIndex) (salts : SaltVector Slot Salt) : Prop :=
  salts (pairLeft pair) = salts (pairRight pair)

include pairDistinct

theorem collision_coordinate_fiber_le_one (pair : PairIndex)
    (tail : OmitCoordinate (Salt := Salt) (pairLeft pair)) :
    Nat.card
      (coordinateFiber (fun _ salts => collisionAt pairLeft pairRight pair salts)
        (pairLeft pair) tail) ≤ 1 := by
  letI : Finite
      (coordinateFiber (fun _ salts => collisionAt pairLeft pairRight pair salts)
        (pairLeft pair) tail) :=
    Finite.of_injective (fun value => value.1)
      (fun _ _ equal => Subtype.ext equal)
  rw [Finite.card_le_one_iff_subsingleton]
  constructor
  intro left right
  apply Subtype.ext
  have leftEq := left.2
  have rightEq := right.2
  simp [coordinateFiber, collisionAt, rebuildCoordinate,
    pairDistinct pair, Ne.symm (pairDistinct pair)] at leftEq rightEq
  exact leftEq.trans rightEq.symm

theorem one_pair_collision_count_le (pair : PairIndex) :
    Nat.card {salts : SaltVector Slot Salt //
      collisionAt pairLeft pairRight pair salts} ≤
      Fintype.card Salt ^ (Fintype.card Slot - 1) := by
  simpa using coordinate_event_count_le
    (fun _ salts => collisionAt pairLeft pairRight pair salts) 1
    (pairLeft pair)
    (fun tail => collision_coordinate_fiber_le_one
      (Salt := Salt) (pairLeft := pairLeft) (pairRight := pairRight)
      (pairDistinct := pairDistinct) pair tail)

omit pairDistinct

def chooseCollision
    (salts : {salts : SaltVector Slot Salt //
      ∃ pair, collisionAt pairLeft pairRight pair salts}) :
    Σ pair : PairIndex, {salts : SaltVector Slot Salt //
      collisionAt pairLeft pairRight pair salts} :=
  let pair := Classical.choose salts.2
  ⟨pair, ⟨salts.1, Classical.choose_spec salts.2⟩⟩

theorem chooseCollision_injective :
    Function.Injective (chooseCollision (Salt := Salt) pairLeft pairRight) := by
  intro left right equal
  apply Subtype.ext
  exact congrArg (fun item : Σ pair : PairIndex,
    {salts : SaltVector Slot Salt // collisionAt pairLeft pairRight pair salts} =>
      item.2.1) equal

include pairDistinct

theorem collision_count_le :
    Nat.card {salts : SaltVector Slot Salt //
      ∃ pair, collisionAt pairLeft pairRight pair salts} ≤
      Fintype.card PairIndex *
        Fintype.card Salt ^ (Fintype.card Slot - 1) := by
  letI : ∀ pair : PairIndex, Finite
      {salts : SaltVector Slot Salt //
        collisionAt pairLeft pairRight pair salts} := fun _ =>
    Finite.of_injective (fun salts => salts.1)
      (fun _ _ equal => Subtype.ext equal)
  letI : Finite (Σ pair : PairIndex,
      {salts : SaltVector Slot Salt //
        collisionAt pairLeft pairRight pair salts}) :=
    Finite.of_injective (fun item => (item.1, item.2.1)) (by
      intro left right equal
      rcases left with ⟨leftIndex, leftSalts⟩
      rcases right with ⟨rightIndex, rightSalts⟩
      simp only [Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, saltsEqual⟩
      have : leftSalts = rightSalts := Subtype.ext saltsEqual
      cases this
      rfl)
  calc
    Nat.card {salts : SaltVector Slot Salt //
        ∃ pair, collisionAt pairLeft pairRight pair salts} ≤
        Nat.card (Σ pair : PairIndex,
          {salts : SaltVector Slot Salt //
            collisionAt pairLeft pairRight pair salts}) :=
      Nat.card_le_card_of_injective
        (chooseCollision (Salt := Salt) pairLeft pairRight)
        (chooseCollision_injective (Salt := Salt) pairLeft pairRight)
    _ = ∑ pair : PairIndex, Nat.card
          {salts : SaltVector Slot Salt //
            collisionAt pairLeft pairRight pair salts} := by
      rw [Nat.card_sigma]
    _ ≤ ∑ _pair : PairIndex,
          Fintype.card Salt ^ (Fintype.card Slot - 1) := by
      exact Finset.sum_le_sum fun pair _ =>
        one_pair_collision_count_le
          (Salt := Salt) (pairLeft := pairLeft) (pairRight := pairRight)
          (pairDistinct := pairDistinct) pair
    _ = Fintype.card PairIndex *
          Fintype.card Salt ^ (Fintype.card Slot - 1) := by simp

omit pairDistinct

def idealBad
    (probe : Slot → SaltVector Slot Salt → Prop)
    (salts : SaltVector Slot Salt) : Prop :=
  (∃ pair, collisionAt pairLeft pairRight pair salts) ∨
    ∃ i, probe i salts

def splitIdealBad
    (probe : Slot → SaltVector Slot Salt → Prop) :
    {salts : SaltVector Slot Salt //
      idealBad pairLeft pairRight probe salts} →
      {salts : SaltVector Slot Salt //
        ∃ pair, collisionAt pairLeft pairRight pair salts} ⊕
      {salts : SaltVector Slot Salt // ∃ i, probe i salts} := by
  classical
  intro salts
  by_cases collision : ∃ pair, collisionAt pairLeft pairRight pair salts.1
  · exact Sum.inl ⟨salts.1, collision⟩
  · exact Sum.inr ⟨salts.1, salts.2.resolve_left collision⟩

theorem splitIdealBad_injective
    (probe : Slot → SaltVector Slot Salt → Prop) :
    Function.Injective (splitIdealBad pairLeft pairRight probe) := by
  classical
  intro left right equal
  apply Subtype.ext
  unfold splitIdealBad at equal
  by_cases leftCollision :
      ∃ pair, collisionAt pairLeft pairRight pair left.1 <;>
    by_cases rightCollision :
      ∃ pair, collisionAt pairLeft pairRight pair right.1 <;>
    simp [leftCollision, rightCollision] at equal
  · exact equal
  · exact equal

include pairDistinct

/-- The universal finite ideal-salt loss, as an exact numerator bound.
Dividing by `|Salt| ^ |Slot|` gives the corresponding uniform probability.
The only external premise is the coordinate-fiber cap. -/
theorem ideal_bad_count_le
    (probe : Slot → SaltVector Slot Salt → Prop) (q : Nat)
    (fiberCap : ∀ i tail, Nat.card (coordinateFiber probe i tail) ≤ q) :
    Nat.card {salts : SaltVector Slot Salt //
      idealBad pairLeft pairRight probe salts} ≤
      (Fintype.card PairIndex + Fintype.card Slot * q) *
        Fintype.card Salt ^ (Fintype.card Slot - 1) := by
  letI : Finite {salts : SaltVector Slot Salt //
      ∃ pair, collisionAt pairLeft pairRight pair salts} :=
    Finite.of_injective (fun salts => salts.1)
      (fun _ _ equal => Subtype.ext equal)
  letI : Finite {salts : SaltVector Slot Salt // ∃ i, probe i salts} :=
    Finite.of_injective (fun salts => salts.1)
      (fun _ _ equal => Subtype.ext equal)
  letI : Finite
      ({salts : SaltVector Slot Salt //
          ∃ pair, collisionAt pairLeft pairRight pair salts} ⊕
       {salts : SaltVector Slot Salt // ∃ i, probe i salts}) :=
    Finite.of_injective
      (Sum.elim (fun salts => Sum.inl salts.1) (fun salts => Sum.inr salts.1)) (by
        intro left right equal
        cases left <;> cases right <;> simp_all [Subtype.ext_iff])
  calc
    Nat.card {salts : SaltVector Slot Salt //
        idealBad pairLeft pairRight probe salts} ≤
        Nat.card
          ({salts : SaltVector Slot Salt //
              ∃ pair, collisionAt pairLeft pairRight pair salts} ⊕
           {salts : SaltVector Slot Salt // ∃ i, probe i salts}) :=
      Nat.card_le_card_of_injective
        (splitIdealBad pairLeft pairRight probe)
        (splitIdealBad_injective pairLeft pairRight probe)
    _ = Nat.card {salts : SaltVector Slot Salt //
          ∃ pair, collisionAt pairLeft pairRight pair salts} +
        Nat.card {salts : SaltVector Slot Salt // ∃ i, probe i salts} := by
      rw [Nat.card_sum]
    _ ≤ Fintype.card PairIndex *
          Fintype.card Salt ^ (Fintype.card Slot - 1) +
        (Fintype.card Slot * q) *
          Fintype.card Salt ^ (Fintype.card Slot - 1) :=
      Nat.add_le_add
        (collision_count_le pairLeft pairRight pairDistinct)
        (adaptive_probe_count_le probe q fiberCap)
    _ = (Fintype.card PairIndex + Fintype.card Slot * q) *
          Fintype.card Salt ^ (Fintype.card Slot - 1) := by
      rw [Nat.add_mul]

def uniformSaltMass (event : SaltVector Slot Salt → Prop) : ℝ :=
  Nat.card {salts : SaltVector Slot Salt // event salts} /
    Fintype.card (SaltVector Slot Salt)

theorem ideal_bad_uniform_mass_le
    (probe : Slot → SaltVector Slot Salt → Prop) (q : Nat)
    (fiberCap : ∀ i tail, Nat.card (coordinateFiber probe i tail) ≤ q) :
    uniformSaltMass (idealBad pairLeft pairRight probe) ≤
      (((Fintype.card PairIndex + Fintype.card Slot * q) *
        Fintype.card Salt ^ (Fintype.card Slot - 1) : Nat) : ℝ) /
        Fintype.card (SaltVector Slot Salt) := by
  unfold uniformSaltMass
  rw [div_le_div_iff_of_pos_right]
  · exact Nat.cast_le.mpr
      (ideal_bad_count_le pairLeft pairRight pairDistinct probe q fiberCap)
  · exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance)

end Collision

#print axioms adaptive_probe_count_le
#print axioms collision_count_le
#print axioms ideal_bad_count_le
#print axioms ideal_bad_uniform_mass_le
end
end AspisV8PairedCommitment
