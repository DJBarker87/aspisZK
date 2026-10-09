import CausalSourcePolynomialTrace
import SelectedRangeLaneCoordinateSlice

/-! Generic chronological source-polynomial constructor.

A caller supplies one fixed multivariate source value and its exact
one-coordinate polynomial slice.  The slice evaluation and degree bounds are
local algebraic obligations.  This file constructs the ten causal messages by
summing over future Boolean suffixes, and proves the initial cube boundary and
all successor boundaries internally.  No `SourcePolynomial`, boundary, or
endpoint is accepted as an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 3000

namespace AspisV8Completion.BooleanSuffixSourceConstructor
open scoped BigOperators
open Polynomial
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SelectedRangeLaneCoordinateSlice

variable {K : Type*} [Field K] [DecidableEq K]

def boolValue : Bool → K
  | false => 0
  | true => 1

/-- Local source interface.  `fixed round` is intentionally irrelevant to a
correct slice; the evaluation law states this extensionally through
`replaceCoordinate`. -/
structure CoordinateSlices where
  value : (Fin 10 → K) → K
  slice : (Fin 10 → K) → Fin 10 → K[X]
  degree : ∀ fixed round, (slice fixed round).natDegree ≤ 27
  eval_at : ∀ fixed round x,
    (slice fixed round).eval x = value (replaceCoordinate fixed round x)

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
  · simp [equal]

noncomputable def restriction (spec : CoordinateSlices (K := K))
    (round : Fin 10) (history : List K) : K[X] :=
  ∑ suffix : Fin (9 - round.val) → Bool,
    spec.slice (futurePoint history round 0 suffix) round

theorem restriction_degree (spec : CoordinateSlices (K := K))
    (round : Fin 10) (history : List K) :
    (restriction spec round history).natDegree ≤ 27 := by
  unfold restriction
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro suffix _
  exact spec.degree _ round

theorem restriction_eval (spec : CoordinateSlices (K := K))
    (round : Fin 10) (history : List K) (x : K) :
    (restriction spec round history).eval x =
      ∑ suffix : Fin (9 - round.val) → Bool,
        spec.value (futurePoint history round x suffix) := by
  simp only [restriction, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro suffix _
  rw [spec.eval_at, replace_futurePoint]

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
    simp_all [futurePoint, boolValue, prependFuture]

theorem restriction_successor_boundary (spec : CoordinateSlices (K := K))
    (previous : Fin 9) (history : List K) (challenge : K)
    (length : history.length = previous.val) :
    (restriction spec previous.succ (history.concat challenge)).eval 0 +
        (restriction spec previous.succ (history.concat challenge)).eval 1 =
      (restriction spec previous.castSucc history).eval challenge := by
  rw [restriction_eval, restriction_eval, restriction_eval]
  rw [sum_prependFuture previous]
  simp only [futurePoint_cons previous history challenge length, boolValue]

def booleanPoint (bits : Fin 10 → Bool) : Fin 10 → K :=
  fun coordinate => boolValue (bits coordinate)

noncomputable def rowBitsEquiv : Fin 1024 ≃ (Fin 10 → Bool) :=
  Equiv.ofBijective (fun row coordinate => bigEndianBit row coordinate)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      bigEndianBits_injective, by simp⟩)

theorem booleanPoint_rowBitsEquiv (row : Fin 1024) :
    booleanPoint (rowBitsEquiv row) = booleanTracePoint (K := K) row := by
  funext coordinate
  change boolValue (bigEndianBit row coordinate) = _
  by_cases bit : bigEndianBit row coordinate <;>
    simp [boolValue, booleanTracePoint, bit]

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

theorem futurePoint_zero_cons (bit : Bool) (tail : Fin 9 → Bool) :
    futurePoint ([] : List K) 0 (boolValue bit) tail =
      booleanPoint (prependTen bit tail) := by
  funext coordinate
  fin_cases coordinate <;> simp [futurePoint, booleanPoint, boolValue, prependTen]

def booleanTable (spec : CoordinateSlices (K := K)) : Fin 1024 → K :=
  fun row => spec.value (booleanTracePoint row)

theorem restriction_initial_boundary (spec : CoordinateSlices (K := K)) :
    (restriction spec 0 []).eval 0 + (restriction spec 0 []).eval 1 =
      ∑ row, booleanTable spec row := by
  rw [restriction_eval, restriction_eval]
  change
    (∑ suffix : Fin 9 → Bool,
      spec.value (futurePoint [] 0 (boolValue false) suffix)) +
    (∑ suffix : Fin 9 → Bool,
      spec.value (futurePoint [] 0 (boolValue true) suffix)) = _
  simp_rw [futurePoint_zero_cons]
  rw [← sum_prependTen (fun bits : Fin 10 → Bool => spec.value (booleanPoint bits))]
  rw [← rowBitsEquiv.sum_comp]
  simp only [booleanTable, booleanPoint_rowBitsEquiv]

/-- The generic constructor.  All ten-round boundary obligations are derived
from the local coordinate-slice interface. -/
noncomputable def source (spec : CoordinateSlices (K := K)) :
    SourcePolynomial (booleanTable spec) where
  restriction := restriction spec
  degree := fun round history _ => restriction_degree spec round history
  initialBoundary := restriction_initial_boundary spec
  successorBoundary := restriction_successor_boundary spec

#print axioms restriction_degree
#print axioms restriction_successor_boundary
#print axioms restriction_initial_boundary
#print axioms source
end AspisV8Completion.BooleanSuffixSourceConstructor
