import SelectedSemanticHelperAggregationV2

/-! Selected 29-lane / ten-coordinate aggregation. The lane order is the
two reverse-Horner loops in pair_forest_semantic_terminal::composition_parts:
four Poseidon lanes, twenty-four packed semantic lanes, then the copy lane.
Tables are fixed after adaptive C2 but BEFORE theta. The point exception is
fixed after theta but before the ten-coordinate equality point; the quadratic
helper exception is fixed before mu. No compact-wire authentication or random
oracle freshness is asserted here.

The Boolean/MLE proofs are narrowly ported from V7's
V5AcceptedTerminalResidualExtraction (bigEndianBits_injective through
uniform_zerocheck_collision_fraction_le_ten), without its old 25-lane or
linear-helper terminal and without importing its wider cache closure.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 200000

namespace AspisV8.SelectedSemanticLaneAggregation
open scoped BigOperators
open Polynomial Finset
open AspisV5FriConcreteEncoderApplicability AspisV8.JointImageGame
open AspisV8.SelectedSemanticHelperAggregation
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

structure RowLanes (K : Type*) where
  poseidon : Fin 4 → K
  semantic : Fin 24 → K
  copy : K

def RowLanes.vector (lanes : RowLanes K) : Fin 29 → K :=
  Fin.append lanes.poseidon (Fin.append lanes.semantic (fun _ : Fin 1 => lanes.copy))

def RowLanes.Zero (lanes : RowLanes K) : Prop :=
  (∀ i, lanes.poseidon i=0) ∧ (∀ i, lanes.semantic i=0) ∧ lanes.copy=0

theorem vector_zero_iff (lanes : RowLanes K) :
    lanes.vector=0 ↔ lanes.Zero := by
  constructor
  · intro zero
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have value := congrFun zero (Fin.castAdd 25 i)
      simpa only [RowLanes.vector, Fin.append_left, Pi.zero_apply] using value
    · intro i
      have value := congrFun zero (Fin.natAdd 4 (Fin.castAdd 1 i))
      simpa only [RowLanes.vector, Fin.append_right, Fin.append_left, Pi.zero_apply] using value
    · have value := congrFun zero (Fin.natAdd 4 (Fin.natAdd 24 (0 : Fin 1)))
      simpa only [RowLanes.vector, Fin.append_right, Pi.zero_apply] using value
  · rintro ⟨poseidon, semantic, copy⟩
    have p : lanes.poseidon=(fun _ => 0) := funext poseidon
    have s : lanes.semantic=(fun _ => 0) := funext semantic
    funext i
    simp [RowLanes.vector, p, s, copy, Fin.append, Fin.addCases]

def rowPolynomial (lanes : RowLanes K) : K[X] :=
  monomialPolynomial lanes.vector

theorem rowPolynomial_degree (lanes : RowLanes K) :
    (rowPolynomial lanes).natDegree ≤ 28 :=
  monomialPolynomial_natDegree_le (by decide : 0 < 29) _

theorem rowPolynomial_zero_iff (lanes : RowLanes K) :
    rowPolynomial lanes=0 ↔ lanes.Zero := by
  rw [← vector_zero_iff]
  constructor
  · intro zero
    funext i
    have value := congrArg (fun p : K[X] => p.coeff i.val) zero
    simpa only [rowPolynomial, monomialPolynomial_coeff, Polynomial.coeff_zero] using value
  · intro zero
    simp [rowPolynomial, zero, monomialPolynomial]

/-- Symbolic concatenation, without unrolling any 29-entry vector. -/
theorem eval_append {m n : Nat} (left : Fin m → K) (right : Fin n → K) (theta : K) :
    (monomialPolynomial (Fin.append left right)).eval theta =
      (monomialPolynomial left).eval theta +
        theta^m*(monomialPolynomial right).eval theta := by
  simp only [monomialPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd, pow_add]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact ascending-power spelling of the two source reverse-Horner loops.
Poseidon occupies 0..3, packed semantics 4..27, and copy occupies 28. -/
theorem selected_row_eval (lanes : RowLanes K) (theta : K) :
    (rowPolynomial lanes).eval theta =
      (monomialPolynomial lanes.poseidon).eval theta + theta^4 *
        ((monomialPolynomial lanes.semantic).eval theta + theta^24*lanes.copy) := by
  unfold rowPolynomial RowLanes.vector
  rw [eval_append, eval_append]
  have last : (monomialPolynomial (fun _ : Fin 1 => lanes.copy)).eval theta=lanes.copy := by
    simp [monomialPolynomial, Fin.sum_univ_succ]
  rw [last]

def thetaTable (lanes : Fin 1024 → RowLanes K) (theta : K) : Fin 1024 → K :=
  fun row => (rowPolynomial (lanes row)).eval theta

def AllRowsZero (lanes : Fin 1024 → RowLanes K) : Prop :=
  ∀ row, (lanes row).Zero

/-- One nonzero row is chosen before theta. Never union over all rows. -/
def badTheta (T : Finset K) (lanes : Fin 1024 → RowLanes K) : Finset K :=
  if bad : ∃ row, rowPolynomial (lanes row)≠0 then
    T.filter fun theta => (rowPolynomial (lanes bad.choose)).eval theta=0
  else ∅

theorem badTheta_card (T : Finset K) (lanes : Fin 1024 → RowLanes K) :
    (badTheta T lanes).card ≤ 28 := by
  classical
  unfold badTheta
  split_ifs with bad
  · exact root_count T _ bad.choose_spec 28 (rowPolynomial_degree _)
  · simp

theorem theta_zero_or_collision (T : Finset K) (lanes : Fin 1024 → RowLanes K)
    (theta : K) (inside : theta∈T) (zero : thetaTable lanes theta=0) :
    AllRowsZero lanes ∨ theta∈badTheta T lanes := by
  classical
  by_cases bad : ∃ row, rowPolynomial (lanes row)≠0
  · right
    rw [badTheta, dif_pos bad]
    exact Finset.mem_filter.mpr ⟨inside, congrFun zero bad.choose⟩
  · left
    intro row
    apply (rowPolynomial_zero_iff _).mp
    by_contra nonzero
    exact bad ⟨row, nonzero⟩

def bigEndianBit (row : Fin 1024) (coordinate : Fin 10) : Bool :=
  Nat.testBit row.val (9-coordinate.val)

def booleanTracePoint (row : Fin 1024) : Fin 10 → K := fun coordinate =>
  if bigEndianBit row coordinate then 1 else 0

def mleRowWeight (point : Fin 10 → K) (row : Fin 1024) : K :=
  ∏ coordinate, if bigEndianBit row coordinate then point coordinate else 1-point coordinate

theorem bigEndianBits_injective :
    Function.Injective (fun row : Fin 1024 => fun coordinate : Fin 10 =>
      bigEndianBit row coordinate) := by
  intro left right equalBits
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases within : bit < 10
  · let coordinate : Fin 10 := ⟨9-bit, by omega⟩
    have equalAtCoordinate := congrFun equalBits coordinate
    change Nat.testBit left.val (9-coordinate.val) =
      Nat.testBit right.val (9-coordinate.val) at equalAtCoordinate
    have coordinateBit : 9-coordinate.val=bit := by simp only [coordinate]; omega
    simpa [coordinateBit] using equalAtCoordinate
  · have tenLe : 10 ≤ bit := by omega
    have powLe : 2^10 ≤ 2^bit := Nat.pow_le_pow_right (by decide) tenLe
    have leftBelow : left.val < 2^bit := by have h := left.isLt; norm_num at h; omega
    have rightBelow : right.val < 2^bit := by have h := right.isLt; norm_num at h; omega
    rw [Nat.testBit_eq_false_of_lt leftBelow, Nat.testBit_eq_false_of_lt rightBelow]

theorem mleRowWeight_booleanTracePoint (selected row : Fin 1024) :
    mleRowWeight (booleanTracePoint selected : Fin 10 → K) row =
      if row=selected then 1 else 0 := by
  classical
  by_cases same : row=selected
  · subst row
    simp only [mleRowWeight]
    apply Finset.prod_eq_one
    intro coordinate _
    by_cases bit : bigEndianBit selected coordinate <;> simp [booleanTracePoint, bit]
  · have differ : (fun c : Fin 10 => bigEndianBit row c) ≠
        (fun c : Fin 10 => bigEndianBit selected c) :=
        fun equal => same (bigEndianBits_injective equal)
    obtain ⟨coordinate, bitDiffers⟩ := Function.ne_iff.mp differ
    rw [if_neg same]
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    by_cases rowBit : bigEndianBit row coordinate
    · have selectedBit : bigEndianBit selected coordinate=false := by
        cases value : bigEndianBit selected coordinate
        · rfl
        · exact False.elim (bitDiffers (by simp [rowBit, value]))
      simp [booleanTracePoint, rowBit, selectedBit]
    · have selectedBit : bigEndianBit selected coordinate=true := by
        cases value : bigEndianBit selected coordinate
        · exact False.elim (bitDiffers (by simp [rowBit, value]))
        · rfl
      simp [booleanTracePoint, rowBit, selectedBit]

/-- Literal equality_value factor, including its two product terms. -/
def sourceEqualityValue (left right : Fin 10 → K) : K :=
  ∏ coordinate, 1-left coordinate-right coordinate+
    left coordinate*right coordinate+left coordinate*right coordinate

theorem sourceEqualityValue_booleanTracePoint (point : Fin 10 → K) (row : Fin 1024) :
    sourceEqualityValue point (booleanTracePoint row)=mleRowWeight point row := by
  classical
  simp only [sourceEqualityValue, mleRowWeight]
  apply Finset.prod_congr rfl
  intro coordinate _
  by_cases bit : bigEndianBit row coordinate <;> simp [booleanTracePoint, bit]

def tableMLEValue (point : Fin 10 → K) (table : Fin 1024 → K) : K :=
  ∑ row, mleRowWeight point row*table row

def mleRowPolynomial (row : Fin 1024) : MvPolynomial (Fin 10) K :=
  ∏ coordinate, if bigEndianBit row coordinate then MvPolynomial.X coordinate
    else 1-MvPolynomial.X coordinate

def tableMLEPolynomial (table : Fin 1024 → K) : MvPolynomial (Fin 10) K :=
  ∑ row, MvPolynomial.C (table row)*mleRowPolynomial row

@[simp] theorem eval_mleRowPolynomial (point : Fin 10 → K) (row : Fin 1024) :
    MvPolynomial.eval point (mleRowPolynomial row)=mleRowWeight point row := by
  classical
  rw [mleRowPolynomial, map_prod]
  simp only [mleRowWeight]
  apply Finset.prod_congr rfl
  intro coordinate _
  by_cases bit : bigEndianBit row coordinate <;> simp [bit]

@[simp] theorem eval_tableMLEPolynomial (point : Fin 10 → K) (table : Fin 1024 → K) :
    MvPolynomial.eval point (tableMLEPolynomial table)=tableMLEValue point table := by
  classical
  simp [tableMLEPolynomial, tableMLEValue, map_sum, mul_comm]

theorem tableMLEValue_booleanTracePoint (table : Fin 1024 → K) (selected : Fin 1024) :
    tableMLEValue (booleanTracePoint selected) table=table selected := by
  classical
  unfold tableMLEValue
  simp_rw [mleRowWeight_booleanTracePoint]
  rw [Finset.sum_eq_single selected]
  · simp
  · intro row _ rowNe
    simp [rowNe]
  · simp

theorem tableMLEPolynomial_ne_zero (table : Fin 1024 → K) (nonzero : table≠0) :
    tableMLEPolynomial table≠0 := by
  classical
  have existsNonzero : ∃ row, table row≠0 := by
    by_contra noNonzero
    apply nonzero
    funext row
    by_contra rowNonzero
    exact noNonzero ⟨row, rowNonzero⟩
  obtain ⟨row, rowNonzero⟩ := existsNonzero
  intro polynomialZero
  have zero := congrArg (MvPolynomial.eval (booleanTracePoint row)) polynomialZero
  rw [map_zero, eval_tableMLEPolynomial, tableMLEValue_booleanTracePoint] at zero
  exact rowNonzero zero

theorem mleRowPolynomial_totalDegree_le (row : Fin 1024) :
    (mleRowPolynomial (K := K) row).totalDegree ≤ 10 := by
  classical
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ coordinate : Fin 10,
        (if bigEndianBit row coordinate then MvPolynomial.X coordinate
          else 1-MvPolynomial.X coordinate : MvPolynomial (Fin 10) K).totalDegree
      ≤ ∑ _coordinate : Fin 10, 1 := by
        apply Finset.sum_le_sum
        intro coordinate _
        by_cases bit : bigEndianBit row coordinate
        · simp [bit]
        · simp only [bit]
          refine (MvPolynomial.totalDegree_sub _ _).trans ?_
          simp
    _ = 10 := by simp

theorem tableMLEPolynomial_totalDegree_le (table : Fin 1024 → K) :
    (tableMLEPolynomial table).totalDegree ≤ 10 := by
  classical
  unfold tableMLEPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro row _
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  calc
    (MvPolynomial.C (table row) : MvPolynomial (Fin 10) K).totalDegree +
        (mleRowPolynomial row).totalDegree
      ≤ 0+10 := Nat.add_le_add (by simp) (mleRowPolynomial_totalDegree_le row)
    _ = 10 := by omega

section Finite
variable [Fintype K]

/-- Empty on the zero-table branch; otherwise the original full point space,
never conditioned on a good prefix or renormalized. -/
def badPoint (table : Fin 1024 → K) : Finset (Fin 10 → K) :=
  if table=0 then ∅ else Finset.univ.filter fun point => tableMLEValue point table=0

theorem badPoint_fraction (table : Fin 1024 → K) :
    ((badPoint table).card : ℚ≥0)/(Fintype.card K^10) ≤
      (10 : ℚ≥0)/Fintype.card K := by
  classical
  by_cases zero : table=0
  · simp [badPoint, zero]
  · have bound := MvPolynomial.schwartz_zippel_totalDegree
      (tableMLEPolynomial_ne_zero table zero) (Finset.univ : Finset K)
    simp only [Fintype.piFinset_univ, Finset.card_univ, eval_tableMLEPolynomial] at bound
    rw [badPoint, if_neg zero]
    refine bound.trans ?_
    gcongr
    exact_mod_cast tableMLEPolynomial_totalDegree_le table

theorem point_zero_or_collision (table : Fin 1024 → K) (point : Fin 10 → K)
    (zero : tableMLEValue point table=0) : table=0 ∨ point∈badPoint table := by
  classical
  by_cases identical : table=0
  · exact Or.inl identical
  · right
    simp only [badPoint, if_neg identical, Finset.mem_filter, Finset.mem_univ, true_and]
    exact zero

/-- Total ideal Boolean-terminal alternative. This consumes a zero sum of
the actual selected three-term oracle spelling, NOT scalar acceptance alone.
The named exceptional sets have respective bounds 28, 10/|K|, and 2, with
the causal fixing visible in their arguments. Later messages are unrestricted.
-/
theorem source_zero_alternative (T S : Finset K)
    (lanes : Fin 1024 → RowLanes K) (helper active : Fin 1024 → K)
    (theta : K) (point : Fin 10 → K) (mu : K)
    (thetaInside : theta∈T) (muInside : mu∈S)
    (zero : (∑ row : Fin 1024,
      unmaskedTable (mleRowWeight point) (thetaTable lanes theta) helper active mu row)=0) :
    (AllRowsZero lanes ∧ (∑ row, helper row)=0 ∧
      (∑ row, (1-active row)*helper row)=0) ∨
    theta∈badTheta T lanes ∨ point∈badPoint (thetaTable lanes theta) ∨
    mu∈badMu S (tableMLEValue point (thetaTable lanes theta))
      (∑ row, helper row) (∑ row, (1-active row)*helper row) := by
  classical
  have first :
      (tableMLEValue point (thetaTable lanes theta)=0 ∧
        (∑ row, helper row)=0 ∧ (∑ row, (1-active row)*helper row)=0) ∨
      mu∈badMu S (tableMLEValue point (thetaTable lanes theta))
        (∑ row, helper row) (∑ row, (1-active row)*helper row) := by
    simpa [tableMLEValue] using source_zero_or_collision Finset.univ (mleRowWeight point)
      (thetaTable lanes theta) helper active S mu muInside (by simpa using zero)
  rcases first with ⟨constraintZero, helperZero, inactiveZero⟩ | collision
  · rcases point_zero_or_collision (thetaTable lanes theta) point constraintZero with
      tableZero | collision
    · rcases theta_zero_or_collision T lanes theta thetaInside tableZero with allZero | collision
      · exact Or.inl ⟨allZero, helperZero, inactiveZero⟩
      · exact Or.inr (Or.inl collision)
    · exact Or.inr (Or.inr (Or.inl collision))
  · exact Or.inr (Or.inr (Or.inr collision))

end Finite

#print axioms vector_zero_iff
#print axioms selected_row_eval
#print axioms rowPolynomial_zero_iff
#print axioms badTheta_card
#print axioms theta_zero_or_collision
#print axioms sourceEqualityValue_booleanTracePoint
#print axioms tableMLEValue_booleanTracePoint
#print axioms tableMLEPolynomial_ne_zero
#print axioms tableMLEPolynomial_totalDegree_le
#print axioms badPoint_fraction
#print axioms source_zero_alternative
end
end AspisV8.SelectedSemanticLaneAggregation
