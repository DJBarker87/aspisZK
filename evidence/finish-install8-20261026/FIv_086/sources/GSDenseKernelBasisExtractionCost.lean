import GSDenseKernelExtractionCost
import CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness
import Mathlib.Tactic
import CompPoly.LinearAlgebra.Dense.RrefShape

set_option autoImplicit false

namespace CompPoly.DenseMatrix

variable {F : Type*}

/-- Cost of producing the production basis vector for each free column in a
list, including the coordinate loop and pivot-row searches already counted by
the focused primitive. -/
def basisVectorListCounted [Field F] [BEq F] (A : DenseMatrix F)
    (pivots : Array Nat) : List Nat → List (Array F) × Nat
  | [] => ([], 0)
  | free :: frees =>
      let here := basisVectorForFreeColumnCounted A pivots free
      let rest := basisVectorListCounted A pivots frees
      (here.1 :: rest.1, here.2 + rest.2)

theorem basisVectorListCounted_refines [Field F] [BEq F]
    (A : DenseMatrix F) (pivots : Array Nat) (frees : List Nat) :
    (basisVectorListCounted A pivots frees).1 =
      frees.map (basisVectorForFreeColumn A pivots) := by
  induction frees with
  | nil => rfl
  | cons free frees ih =>
      simp [basisVectorListCounted, basisVectorForFreeColumnCounted_refines, ih]

theorem basisVectorListCounted_cost_le [Field F] [BEq F]
    (A : DenseMatrix F) (pivots : Array Nat) (frees : List Nat) :
    (basisVectorListCounted A pivots frees).2 ≤
      frees.length * (A.cols * (pivots.size + 1)) := by
  induction frees with
  | nil => simp [basisVectorListCounted]
  | cons free frees ih =>
      simp only [basisVectorListCounted, Prod.snd]
      have hone := basisVectorForFreeColumnCounted_cost_le A pivots free
      simp only [List.length_cons]
      rw [Nat.succ_mul]
      omega

private theorem listFilterLengthLe {α : Type*} (p : α → Bool) (xs : List α) :
    (xs.filter p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      cases h : p x <;> simp [h, ih] <;> omega

/-- Count the actual free-column filter and exact production basis-vector
construction. This is extraction work only; RREF work is charged separately. -/
def homogeneousKernelBasisExtractionCounted [Field F] [BEq F]
    (R : RrefResult F) : Array (Array F) × Nat :=
  let free := freeColumnsCounted R.matrix.cols R.pivots
  let vectors := basisVectorListCounted R.matrix R.pivots free.1.toList
  (vectors.1.toArray, free.2 + vectors.2)

theorem homogeneousKernelBasisExtractionCounted_refines [Field F] [BEq F]
    (R : RrefResult F) :
    (homogeneousKernelBasisExtractionCounted R).1 =
      (freeColumns R.matrix.cols R.pivots).map
        (basisVectorForFreeColumn R.matrix R.pivots) := by
  apply Array.ext
  · simp [homogeneousKernelBasisExtractionCounted,
      freeColumnsCounted_refines, basisVectorListCounted_refines]
  · intro i hi1 hi2
    simp [homogeneousKernelBasisExtractionCounted,
      freeColumnsCounted_refines, basisVectorListCounted_refines]

theorem freeColumnsCounted_size_le [Field F] [BEq F]
    (cols : Nat) (pivots : Array Nat) :
    (freeColumnsCounted cols pivots).1.size ≤ cols := by
  rw [freeColumnsCounted_refines]
  change ((List.range cols).filter _).length ≤ cols
  exact Nat.le_trans (listFilterLengthLe _ _) (by simp)

theorem homogeneousKernelBasisExtractionCounted_cost_le [Field F] [BEq F]
    (R : RrefResult F) :
    (homogeneousKernelBasisExtractionCounted R).2 ≤
      R.matrix.cols * (R.pivots.size + 1) * (R.matrix.cols + 1) := by
  let free := freeColumnsCounted R.matrix.cols R.pivots
  let vectors := basisVectorListCounted R.matrix R.pivots free.1.toList
  have hfreeCost := freeColumnsCounted_cost_le R.matrix.cols R.pivots
  have hvectors := basisVectorListCounted_cost_le R.matrix R.pivots free.1.toList
  have hfreeSize := freeColumnsCounted_size_le (F := F) R.matrix.cols R.pivots
  have hlistSize : free.1.toList.length ≤ R.matrix.cols := by
    simpa [free] using hfreeSize
  have hvectors' : vectors.2 ≤ R.matrix.cols *
      (R.matrix.cols * (R.pivots.size + 1)) := by
    dsimp [vectors]
    exact le_trans hvectors (Nat.mul_le_mul_right _ hlistSize)
  change free.2 + vectors.2 ≤ _
  calc
    free.2 + vectors.2 ≤
        R.matrix.cols * (R.pivots.size + 1) +
          R.matrix.cols * (R.matrix.cols * (R.pivots.size + 1)) :=
      Nat.add_le_add hfreeCost hvectors'
    _ = R.matrix.cols * (R.pivots.size + 1) * (R.matrix.cols + 1) := by ring

/-- The fully counted in-place extraction returns exactly the maintained
production basis. Its count combines the accepted RREF work count with actual
free-column and basis-vector loop counts. -/
def homogeneousKernelBasisInPlaceFullCounted [Field F] [BEq F]
    (M : DenseMatrix F) : Array (Array F) × Nat :=
  let rr := rrefLoopDataFullWorkCounted (M.cols + 1) M.rows M.cols 0 0 M.data #[]
  let R : RrefResult F :=
    { matrix := { rows := M.rows, cols := M.cols, data := rr.1.1 }, pivots := rr.1.2 }
  let extraction := homogeneousKernelBasisExtractionCounted R
  (extraction.1, rr.2 + extraction.2)

theorem homogeneousKernelBasisInPlaceFullCounted_refines [Field F] [BEq F]
    (M : DenseMatrix F) :
    (homogeneousKernelBasisInPlaceFullCounted M).1 = homogeneousKernelBasisInPlace M := by
  simp [homogeneousKernelBasisInPlaceFullCounted,
    rrefLoopDataFullWorkCounted_refines,
    homogeneousKernelBasisExtractionCounted_refines,
    homogeneousKernelBasisInPlace, rrefInPlace]

theorem homogeneousKernelBasisInPlaceFullCounted_cost_le [Field F] [BEq F]
    (M : DenseMatrix F) :
    (homogeneousKernelBasisInPlaceFullCounted M).2 ≤
      (M.cols + 1) * (M.rows + M.cols + (M.rows + 1) * M.cols) +
        M.cols * (M.rows + 1) * (M.cols + 1) := by
  let rr := rrefLoopDataFullWorkCounted (M.cols + 1) M.rows M.cols 0 0 M.data #[]
  let R : RrefResult F :=
    { matrix := { rows := M.rows, cols := M.cols, data := rr.1.1 }, pivots := rr.1.2 }
  let extraction := homogeneousKernelBasisExtractionCounted R
  have hloop : rr.2 ≤
      (M.cols + 1) * (M.rows + M.cols + (M.rows + 1) * M.cols) := by
    simpa [rr] using rrefLoopDataFullWorkCounted_initial_le M.rows M.cols M.data #[]
  have hpivots : R.pivots.size ≤ M.rows := by
    have hR : R = rrefInPlace M := by
      cases M with
      | mk rows cols data =>
        simp [R, rr, rrefInPlace, rrefLoopDataFullWorkCounted_refines]
    rw [hR, rrefInPlace_eq]
    exact rref_pivots_size_le_rows M
  have hextract := homogeneousKernelBasisExtractionCounted_cost_le R
  have hfactor : M.cols * (R.pivots.size + 1) ≤ M.cols * (M.rows + 1) :=
    Nat.mul_le_mul_left M.cols (Nat.succ_le_succ hpivots)
  have hfactor' := Nat.mul_le_mul_right (M.cols + 1) hfactor
  change rr.2 + extraction.2 ≤ _
  exact Nat.add_le_add hloop (le_trans hextract hfactor')

/-- Selecting the first extracted basis vector is an additional constant-size
branch. -/
def homogeneousWitnessInPlaceFullCounted [Field F] [BEq F]
    (M : DenseMatrix F) : Option (Array F) × Nat :=
  let basis := homogeneousKernelBasisInPlaceFullCounted M
  (if basis.1.size = 0 then none else some (basis.1.getD 0 #[]), basis.2 + 1)

theorem homogeneousWitnessInPlaceFullCounted_refines [Field F] [BEq F]
    (M : DenseMatrix F) :
    (homogeneousWitnessInPlaceFullCounted M).1 = homogeneousWitnessInPlace M := by
  simp [homogeneousWitnessInPlaceFullCounted, homogeneousKernelBasisInPlaceFullCounted_refines,
    homogeneousWitnessInPlace]

theorem homogeneousWitnessInPlaceFullCounted_cost_le [Field F] [BEq F]
    (M : DenseMatrix F) :
    (homogeneousWitnessInPlaceFullCounted M).2 ≤
      (M.cols + 1) * (M.rows + M.cols + (M.rows + 1) * M.cols) +
        M.cols * (M.rows + 1) * (M.cols + 1) + 1 := by
  change (homogeneousKernelBasisInPlaceFullCounted M).2 + 1 ≤ _
  exact Nat.add_le_add_right (homogeneousKernelBasisInPlaceFullCounted_cost_le M) 1

#print axioms basisVectorListCounted_refines
#print axioms basisVectorListCounted_cost_le
#print axioms homogeneousKernelBasisExtractionCounted_refines
#print axioms homogeneousKernelBasisExtractionCounted_cost_le
#print axioms homogeneousKernelBasisInPlaceFullCounted_refines
#print axioms homogeneousKernelBasisInPlaceFullCounted_cost_le
#print axioms homogeneousWitnessInPlaceFullCounted_refines
#print axioms homogeneousWitnessInPlaceFullCounted_cost_le

end CompPoly.DenseMatrix
