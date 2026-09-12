import SelectedRangeLaneCoordinateSlice
import CausalSourcePolynomialTrace

/-! Chronological Boolean-suffix trace for one literal selected range lane.

The committed trace-column table is fixed before this constructor is used.
At round `r`, the message depends only on the `r` preceding challenges: it
sums the exact degree-three coordinate slice over every Boolean assignment to
the future coordinates.  The adjacent-round law is the head/tail partition of
that suffix space, rather than an assumed callback equality.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 3000

namespace AspisV8Completion.SelectedRangeLaneSourcePolynomial
open scoped BigOperators
open Polynomial
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SelectedRangeLaneCoordinateSlice

variable {K : Type*} [Field K] [DecidableEq K]

def boolValue : Bool → K
  | false => 0
  | true => 1

/-- Complete a visible history, one current coordinate, and a Boolean future
suffix into a ten-coordinate point. -/
def futurePoint (history : List K) (round : Fin 10) (current : K)
    (suffix : Fin (9 - round.val) → Bool) : Fin 10 → K := fun coordinate =>
  if before : coordinate.val < round.val then history.getD coordinate.val 0
  else if equal : coordinate = round then current
  else boolValue (suffix ⟨coordinate.val - round.val - 1, by omega⟩)

theorem replace_futurePoint (history : List K) (round : Fin 10)
    (suffix : Fin (9 - round.val) → Bool) (x : K) :
    replaceCoordinate (futurePoint history round 0 suffix) round x =
      futurePoint history round x suffix := by
  funext coordinate
  unfold replaceCoordinate futurePoint
  by_cases equal : coordinate = round
  · subst coordinate
    simp
  · have unequalValues : coordinate.val ≠ round.val := by
      intro same
      exact equal (Fin.ext same)
    simp [equal, unequalValues]

/-- Source message before challenge `round`. -/
noncomputable def restriction (table : Fin 1024 → K) (round : Fin 10)
    (history : List K) : K[X] :=
  ∑ suffix : Fin (9 - round.val) → Bool,
    rangeLaneSlice table (futurePoint history round 0 suffix) round

theorem restriction_degree_three (table : Fin 1024 → K) (round : Fin 10)
    (history : List K) :
    (restriction table round history).natDegree ≤ 3 := by
  unfold restriction
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro suffix _
  exact rangeLaneSlice_degree table _ round

theorem restriction_degree (table : Fin 1024 → K) (round : Fin 10)
    (history : List K) :
    (restriction table round history).natDegree ≤ 27 :=
  (restriction_degree_three table round history).trans (by omega)

theorem restriction_eval (table : Fin 1024 → K) (round : Fin 10)
    (history : List K) (x : K) :
    (restriction table round history).eval x =
      ∑ suffix : Fin (9 - round.val) → Bool,
        rangeLaneValue table (futurePoint history round x suffix) := by
  simp only [restriction, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro suffix _
  rw [rangeLaneSlice_eval_at, replace_futurePoint]

theorem sum_fin_cons {n : Nat} (f : (Fin (n + 1) → Bool) → K) :
    (∑ suffix, f suffix) =
      (∑ tail : Fin n → Bool, f (Fin.cons false tail)) +
      ∑ tail : Fin n → Bool, f (Fin.cons true tail) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  ac_rfl

def prependFuture (previous : Fin 9) (bit : Bool)
    (tail : Fin (9 - previous.succ.val) → Bool) :
    Fin (9 - previous.castSucc.val) → Bool := fun coordinate =>
  if zero : coordinate.val = 0 then bit
  else tail ⟨coordinate.val - 1, by
    have bound := coordinate.isLt
    simp only [Fin.val_castSucc] at bound
    simp only [Fin.val_succ]
    omega⟩

def dropFuture (previous : Fin 9)
    (suffix : Fin (9 - previous.castSucc.val) → Bool) :
    Fin (9 - previous.succ.val) → Bool := fun coordinate =>
  suffix ⟨coordinate.val + 1, by
    have bound := coordinate.isLt
    simp only [Fin.val_succ] at bound
    simp only [Fin.val_castSucc]
    omega⟩

def prependFutureEquiv (previous : Fin 9) :
    Bool × (Fin (9 - previous.succ.val) → Bool) ≃
      (Fin (9 - previous.castSucc.val) → Bool) where
  toFun pair := prependFuture previous pair.1 pair.2
  invFun suffix := (suffix ⟨0, by
    simp only [Fin.val_castSucc]
    omega⟩, dropFuture previous suffix)
  left_inv pair := by
    rcases pair with ⟨bit, tail⟩
    apply Prod.ext
    · simp [prependFuture]
    · funext coordinate
      simp [dropFuture, prependFuture]
  right_inv suffix := by
    funext coordinate
    by_cases zero : coordinate.val = 0
    · have coordinateZero : coordinate = ⟨0, by
          simp only [Fin.val_castSucc]
          omega⟩ := Fin.ext zero
      rw [coordinateZero]
      simp [prependFuture]
    · simp only [prependFuture, zero, ↓reduceDIte, dropFuture]
      apply congrArg suffix
      apply Fin.ext
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr zero)

theorem sum_prependFuture (previous : Fin 9)
    (f : (Fin (9 - previous.castSucc.val) → Bool) → K) :
    (∑ suffix, f suffix) =
      (∑ tail, f (prependFuture previous false tail)) +
      ∑ tail, f (prependFuture previous true tail) := by
  rw [← (prependFutureEquiv previous).sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  ac_rfl

theorem futurePoint_cons (previous : Fin 9) (history : List K)
    (challenge : K) (length : history.length = previous.val)
    (bit : Bool) (tail : Fin (9 - previous.succ.val) → Bool) :
    futurePoint history previous.castSucc challenge
        (prependFuture previous bit tail) =
      futurePoint (history.concat challenge) previous.succ (boolValue bit) tail := by
  funext coordinate
  fin_cases previous <;> fin_cases coordinate <;>
    simp_all [futurePoint, boolValue, List.getD_append, List.getD_append_right,
      prependFuture]

theorem restriction_successor_boundary (table : Fin 1024 → K)
    (previous : Fin 9) (history : List K) (challenge : K)
    (length : history.length = previous.val) :
    (restriction table previous.succ (history.concat challenge)).eval 0 +
        (restriction table previous.succ (history.concat challenge)).eval 1 =
      (restriction table previous.castSucc history).eval challenge := by
  rw [restriction_eval, restriction_eval, restriction_eval]
  rw [sum_prependFuture previous]
  simp only [futurePoint_cons previous history challenge length, boolValue]

def booleanPoint (bits : Fin 10 → Bool) : Fin 10 → K :=
  fun coordinate => boolValue (bits coordinate)

/-- The selected big-endian decoder is a bijection onto the ten-bit Boolean
cube.  Injectivity is the already-proved selected row theorem; equal finite
cardinality supplies surjectivity. -/
noncomputable def rowBitsEquiv : Fin 1024 ≃ (Fin 10 → Bool) :=
  Equiv.ofBijective
    (fun row coordinate => AspisV8.SelectedSemanticLaneAggregation.bigEndianBit row coordinate)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      AspisV8.SelectedSemanticLaneAggregation.bigEndianBits_injective,
      by simp⟩)

theorem booleanPoint_rowBitsEquiv (row : Fin 1024) :
    booleanPoint (rowBitsEquiv row) =
      AspisV8.SelectedSemanticLaneAggregation.booleanTracePoint (K := K) row := by
  funext coordinate
  change boolValue
      (AspisV8.SelectedSemanticLaneAggregation.bigEndianBit row coordinate) = _
  by_cases bit : AspisV8.SelectedSemanticLaneAggregation.bigEndianBit row coordinate <;>
    simp [booleanPoint, boolValue,
      AspisV8.SelectedSemanticLaneAggregation.booleanTracePoint, bit]

def prependTen (bit : Bool) (tail : Fin 9 → Bool) : Fin 10 → Bool :=
  fun coordinate => if coordinate.val = 0 then bit
    else tail ⟨coordinate.val - 1, by have := coordinate.isLt; omega⟩

def dropTen (bits : Fin 10 → Bool) : Fin 9 → Bool :=
  fun coordinate => bits ⟨coordinate.val + 1, by have := coordinate.isLt; omega⟩

def prependTenEquiv : Bool × (Fin 9 → Bool) ≃ (Fin 10 → Bool) where
  toFun pair := prependTen pair.1 pair.2
  invFun bits := (bits 0, dropTen bits)
  left_inv pair := by
    rcases pair with ⟨bit, tail⟩
    apply Prod.ext
    · simp [prependTen]
    · funext coordinate
      simp [dropTen, prependTen]
  right_inv bits := by
    funext coordinate
    by_cases zero : coordinate.val = 0
    · have coordinateZero : coordinate = 0 := Fin.ext zero
      subst coordinate
      simp [prependTen]
    · simp [prependTen, dropTen, zero]
      have positive : 1 ≤ coordinate.val := Nat.one_le_iff_ne_zero.mpr zero
      have indexEquality :
          (⟨coordinate.val - 1 + 1, by omega⟩ : Fin 10) = coordinate := by
        apply Fin.ext
        exact Nat.sub_add_cancel positive
      rw [indexEquality]

theorem sum_prependTen (f : (Fin 10 → Bool) → K) :
    (∑ bits, f bits) =
      (∑ tail, f (prependTen false tail)) +
      ∑ tail, f (prependTen true tail) := by
  rw [← prependTenEquiv.sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  ac_rfl

def rangeLaneBooleanTable (table : Fin 1024 → K) : Fin 1024 → K :=
  fun row => rangeLaneValue table
    (AspisV8.SelectedSemanticLaneAggregation.booleanTracePoint row)

theorem futurePoint_zero_cons (bit : Bool) (tail : Fin 9 → Bool) :
    futurePoint ([] : List K) 0 (boolValue bit) tail =
      booleanPoint (prependTen bit tail) := by
  funext coordinate
  fin_cases coordinate <;> simp [futurePoint, booleanPoint, boolValue, prependTen]

theorem restriction_initial_boundary (table : Fin 1024 → K) :
    (restriction table 0 []).eval 0 + (restriction table 0 []).eval 1 =
      ∑ row, rangeLaneBooleanTable table row := by
  rw [restriction_eval, restriction_eval]
  change
    (∑ suffix : Fin 9 → Bool,
      rangeLaneValue table (futurePoint [] 0 (boolValue false) suffix)) +
    (∑ suffix : Fin 9 → Bool,
      rangeLaneValue table (futurePoint [] 0 (boolValue true) suffix)) = _
  simp_rw [futurePoint_zero_cons]
  rw [← sum_prependTen (fun bits : Fin 10 → Bool =>
    rangeLaneValue table (booleanPoint bits))]
  rw [← rowBitsEquiv.sum_comp]
  simp only [rangeLaneBooleanTable, booleanPoint_rowBitsEquiv]

/-- The literal range-lane source packaged with all chronological boundaries.
The table is fixed and no endpoint equation is supplied. -/
noncomputable def source (table : Fin 1024 → K) :
    SourcePolynomial (rangeLaneBooleanTable table) where
  restriction := restriction table
  degree := fun round history _ => restriction_degree table round history
  initialBoundary := restriction_initial_boundary table
  successorBoundary := restriction_successor_boundary table

#print axioms restriction_degree
#print axioms restriction_successor_boundary
#print axioms restriction_initial_boundary
#print axioms source
end AspisV8Completion.SelectedRangeLaneSourcePolynomial
