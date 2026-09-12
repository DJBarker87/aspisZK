import SelectedBooleanitySourcePolynomial
import CanonicalTableReferenceTrace

/-! Exact one-coordinate restriction of the selected range lane.

The literal `add_value_lanes` source multiplies each Booleanity residual of an
opened trace column by the sum of the row selectors 1008, 1010 and 1012.  An
opening is a multilinear table polynomial, not a challenge coordinate.  This
leaf constructs the actual univariate restriction of

`(eq_1008 + eq_1010 + eq_1012) * (opening^2 - opening)`

when one challenge coordinate remains variable.  Both the selector and the
opening restrictions are linear, so the source residual has degree at most
three (hence at most 27).  Evaluation at the fixed coordinate is proved equal
to the selected source expression.

This is the local polynomial used in every summand of a causal Boolean-suffix
partial sum.  The suffix enumeration and its adjacent-round partition remain
the next constructor seam; this file does not manufacture a
`SourcePolynomial` from Boolean-table equality. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000

namespace AspisV8Completion.SelectedRangeLaneCoordinateSlice
open scoped BigOperators
open Polynomial
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.CanonicalTableReferenceTrace

variable {K : Type*} [Field K] [DecidableEq K]

/-- The literal three rows selected by `VALUE_AUXILIARY_BLOCK = 63` and local
offsets `[0, 2, 4]`. -/
def rangeRow : Fin 3 → Fin 1024
  | 0 => ⟨1008, by decide⟩
  | 1 => ⟨1010, by decide⟩
  | 2 => ⟨1012, by decide⟩

/-- Restrict one equality polynomial to coordinate `round`, with every other
coordinate supplied by `fixed`.  The value of `fixed round` is intentionally
unused. -/
noncomputable def rowSlice (fixed : Fin 10 → K) (round : Fin 10)
    (row : Fin 1024) : K[X] :=
  C (∏ coordinate ∈ (Finset.univ.erase round), pointFactor fixed row coordinate) *
    bitPolynomial row round

def replaceCoordinate (fixed : Fin 10 → K) (round : Fin 10) (x : K) :
    Fin 10 → K := fun coordinate => if coordinate = round then x else fixed coordinate

theorem rowSlice_degree (fixed : Fin 10 → K) (round : Fin 10)
    (row : Fin 1024) :
    (rowSlice fixed round row).natDegree ≤ 1 := by
  unfold rowSlice
  refine (natDegree_C_mul_le _ _).trans ?_
  by_cases bit : bigEndianBit row round
  · simp [bitPolynomial, bit]
  · rw [bitPolynomial, if_neg bit]
    simpa using natDegree_sub_le (1 : K[X]) X

theorem rowSlice_eval (fixed : Fin 10 → K) (round : Fin 10)
    (row : Fin 1024) :
    (rowSlice fixed round row).eval (fixed round) = mleRowWeight fixed row := by
  unfold rowSlice mleRowWeight
  rw [eval_mul, eval_C, eval_bitPolynomial]
  unfold pointFactor
  rw [Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ round)]

theorem rowSlice_eval_at (fixed : Fin 10 → K) (round : Fin 10)
    (row : Fin 1024) (x : K) :
    (rowSlice fixed round row).eval x =
      mleRowWeight (replaceCoordinate fixed round x) row := by
  unfold rowSlice mleRowWeight
  rw [eval_mul, eval_C, eval_bitPolynomial]
  unfold pointFactor replaceCoordinate
  rw [Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ round)]
  congr 1
  · apply Finset.prod_congr rfl
    intro coordinate membership
    have different : coordinate ≠ round := Finset.ne_of_mem_erase membership
    simp [different]
  · simp

/-- The opening polynomial restricted to one coordinate. -/
noncomputable def openingSlice (table : Fin 1024 → K)
    (fixed : Fin 10 → K) (round : Fin 10) : K[X] :=
  ∑ row, C (table row) * rowSlice fixed round row

theorem openingSlice_degree (table : Fin 1024 → K)
    (fixed : Fin 10 → K) (round : Fin 10) :
    (openingSlice table fixed round).natDegree ≤ 1 := by
  unfold openingSlice
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro row _
  exact (natDegree_C_mul_le (table row) (rowSlice fixed round row)).trans
    (rowSlice_degree fixed round row)

theorem openingSlice_eval (table : Fin 1024 → K)
    (fixed : Fin 10 → K) (round : Fin 10) :
    (openingSlice table fixed round).eval (fixed round) =
      tableMLEValue fixed table := by
  simp only [openingSlice, Polynomial.eval_finsetSum, eval_mul, eval_C,
    rowSlice_eval, tableMLEValue]
  apply Finset.sum_congr rfl
  intro row _
  exact mul_comm _ _

theorem openingSlice_eval_at (table : Fin 1024 → K)
    (fixed : Fin 10 → K) (round : Fin 10) (x : K) :
    (openingSlice table fixed round).eval x =
      tableMLEValue (replaceCoordinate fixed round x) table := by
  simp only [openingSlice, Polynomial.eval_finsetSum, eval_mul, eval_C,
    rowSlice_eval_at, tableMLEValue]
  apply Finset.sum_congr rfl
  intro row _
  exact mul_comm _ _

/-- The exact three-row range selector restricted to one coordinate. -/
noncomputable def rangeSelectorSlice (fixed : Fin 10 → K)
    (round : Fin 10) : K[X] :=
  ∑ which : Fin 3, rowSlice fixed round (rangeRow which)

theorem rangeSelectorSlice_degree (fixed : Fin 10 → K)
    (round : Fin 10) :
    (rangeSelectorSlice fixed round).natDegree ≤ 1 := by
  unfold rangeSelectorSlice
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro which _
  exact rowSlice_degree fixed round (rangeRow which)

def rangeSelectorValue (point : Fin 10 → K) : K :=
  ∑ which : Fin 3, mleRowWeight point (rangeRow which)

theorem rangeSelectorSlice_eval (fixed : Fin 10 → K)
    (round : Fin 10) :
    (rangeSelectorSlice fixed round).eval (fixed round) =
      rangeSelectorValue fixed := by
  simp [rangeSelectorSlice, rangeSelectorValue, Polynomial.eval_finsetSum,
    rowSlice_eval]

theorem rangeSelectorSlice_eval_at (fixed : Fin 10 → K)
    (round : Fin 10) (x : K) :
    (rangeSelectorSlice fixed round).eval x =
      rangeSelectorValue (replaceCoordinate fixed round x) := by
  simp [rangeSelectorSlice, rangeSelectorValue, Polynomial.eval_finsetSum,
    rowSlice_eval_at]

/-- Coordinate restriction of one literal selected range residual. -/
noncomputable def rangeLaneSlice (table : Fin 1024 → K)
    (fixed : Fin 10 → K) (round : Fin 10) : K[X] :=
  let opening := openingSlice table fixed round
  rangeSelectorSlice fixed round * (opening ^ 2 - opening)

theorem rangeLaneSlice_degree (table : Fin 1024 → K)
    (fixed : Fin 10 → K) (round : Fin 10) :
    (rangeLaneSlice table fixed round).natDegree ≤ 3 := by
  let opening := openingSlice table fixed round
  have openingDegree : opening.natDegree ≤ 1 :=
    openingSlice_degree table fixed round
  have squareDegree : (opening ^ 2).natDegree ≤ 2 := by
    calc
      (opening ^ 2).natDegree ≤ 2 * opening.natDegree := natDegree_pow_le
      _ ≤ 2 := by omega
  have residualDegree : (opening ^ 2 - opening).natDegree ≤ 2 :=
    (natDegree_sub_le (opening ^ 2) opening).trans (max_le squareDegree (by omega))
  unfold rangeLaneSlice
  change (rangeSelectorSlice fixed round * (opening ^ 2 - opening)).natDegree ≤ 3
  calc
    _ ≤ (rangeSelectorSlice fixed round).natDegree +
        (opening ^ 2 - opening).natDegree := natDegree_mul_le
    _ ≤ 1 + 2 := Nat.add_le_add (rangeSelectorSlice_degree fixed round)
      residualDegree
    _ = 3 := rfl

def rangeLaneValue (table : Fin 1024 → K) (point : Fin 10 → K) : K :=
  rangeSelectorValue point *
    (tableMLEValue point table ^ 2 - tableMLEValue point table)

theorem rangeLaneSlice_eval (table : Fin 1024 → K)
    (fixed : Fin 10 → K) (round : Fin 10) :
    (rangeLaneSlice table fixed round).eval (fixed round) =
      rangeLaneValue table fixed := by
  unfold rangeLaneSlice
  dsimp only
  rw [eval_mul, eval_sub, eval_pow, rangeSelectorSlice_eval,
    openingSlice_eval]
  rfl

theorem rangeLaneSlice_eval_at (table : Fin 1024 → K)
    (fixed : Fin 10 → K) (round : Fin 10) (x : K) :
    (rangeLaneSlice table fixed round).eval x =
      rangeLaneValue table (replaceCoordinate fixed round x) := by
  unfold rangeLaneSlice
  dsimp only
  rw [eval_mul, eval_sub, eval_pow, rangeSelectorSlice_eval_at,
    openingSlice_eval_at]
  rfl

theorem rangeLaneSlice_degree_le_source_bound (table : Fin 1024 → K)
    (fixed : Fin 10 → K) (round : Fin 10) :
    (rangeLaneSlice table fixed round).natDegree ≤ 27 :=
  (rangeLaneSlice_degree table fixed round).trans (by omega)

#print axioms rowSlice_eval
#print axioms rowSlice_eval_at
#print axioms openingSlice_degree
#print axioms openingSlice_eval
#print axioms rangeSelectorSlice_eval
#print axioms rangeLaneSlice_degree
#print axioms rangeLaneSlice_eval
#print axioms rangeLaneSlice_eval_at
#print axioms rangeLaneSlice_degree_le_source_bound
end AspisV8Completion.SelectedRangeLaneCoordinateSlice
