import AspisFormal.V5FriNaturalBasisRadix4
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-! Exact natural-basis identities for a four-lane sparse lift and its fibre
mean projection. This file uses the source-level dot-product evaluator. The
bridge from that evaluator to `naturalCoefficientPolynomial.eval` is deferred
to the existing `naturalCoefficientPolynomial_eval_eq_sum` theorem; no
protocol or encoder security property is established here. -/

set_option autoImplicit false

noncomputable section

namespace AspisR1

open scoped BigOperators
open AspisCircleTensorBinding
open AspisV5FriNaturalBasisRadix4

variable {K : Type*} [Field K]

/-- The source-level natural-basis dot-product evaluator. -/
def naturalEval {n : Nat} (m : Fin n → K) (x : K) : K :=
  ∑ i : Fin n, m i * naturalLineValue x i

/-- Parent index in a flat fibre-major vector. -/
def parentIndex {n : Nat} (k : Fin (4 * n)) : Fin n :=
  ⟨k.val / 4, by omega⟩

/-- Radix-four slot in a flat fibre-major vector. -/
def slotIndex {n : Nat} (k : Fin (4 * n)) : Fin 4 :=
  ⟨k.val % 4, Nat.mod_lt _ (by decide)⟩

/-- Flat fibre-major index of a parent and one radix-four slot. -/
def childIndex {n : Nat} (i : Fin n) (slot : Fin 4) : Fin (4 * n) :=
  ⟨4 * i.val + slot.val, by omega⟩

@[simp] theorem childIndex_val {n : Nat} (i : Fin n) (slot : Fin 4) :
    (childIndex i slot).val = 4 * i.val + slot.val := rfl

@[simp] theorem parentIndex_childIndex {n : Nat} (i : Fin n) (slot : Fin 4) :
    parentIndex (childIndex i slot) = i := by
  apply Fin.ext
  simp only [parentIndex, childIndex_val]
  omega

@[simp] theorem slotIndex_childIndex {n : Nat} (i : Fin n) (slot : Fin 4) :
    slotIndex (childIndex i slot) = slot := by
  apply Fin.ext
  simp only [slotIndex, childIndex_val]
  omega

@[simp] theorem childIndex_parentIndex_slotIndex {n : Nat}
    (k : Fin (4 * n)) : childIndex (parentIndex k) (slotIndex k) = k := by
  apply Fin.ext
  simp only [childIndex_val, parentIndex, slotIndex]
  omega

/-- Reindex a flat vector by parent and lane. -/
def fibreIndexEquiv (n : Nat) : Fin n × Fin 4 ≃ Fin (4 * n) where
  toFun pair := childIndex pair.1 pair.2
  invFun k := (parentIndex k, slotIndex k)
  left_inv pair := by
    rcases pair with ⟨i, slot⟩
    simp
  right_inv k := childIndex_parentIndex_slotIndex k

@[simp] theorem fibreIndexEquiv_apply {n : Nat} (pair : Fin n × Fin 4) :
    fibreIndexEquiv n pair = childIndex pair.1 pair.2 := rfl

/-- Coefficients in one of the four adjacent lanes. -/
def laneCoefficients (n : Nat) (slot : Fin 4)
    (a : Fin (4 * n) → K) : Fin n → K :=
  fun i => a (childIndex i slot)

/-- Embed a vector into the low coefficient lane, setting the other lanes to
zero. -/
def sparseLift {n : Nat} (m : Fin n → K) : Fin (4 * n) → K := fun k =>
  if slotIndex k = 0 then m (parentIndex k) else 0

@[simp] theorem laneCoefficients_sparseLift {n : Nat} (m : Fin n → K)
    (slot : Fin 4) :
    laneCoefficients n slot (sparseLift m) = if slot = 0 then m else 0 := by
  funext i
  by_cases h : slot = 0 <;> simp [laneCoefficients, sparseLift, h]

theorem sparseLift_injective {n : Nat} :
    Function.Injective (sparseLift (K := K) (n := n)) := by
  intro m₁ m₂ h
  have h0 := congrArg (laneCoefficients n 0) h
  simpa using h0

theorem sparseLift_add {n : Nat} (m₁ m₂ : Fin n → K) :
    sparseLift (m₁ + m₂) = sparseLift m₁ + sparseLift m₂ := by
  funext k
  by_cases h : slotIndex k = 0 <;> simp [sparseLift, h]

theorem sparseLift_smul {n : Nat} (c : K) (m : Fin n → K) :
    sparseLift (c • m) = c • sparseLift m := by
  funext k
  by_cases h : slotIndex k = 0 <;> simp [sparseLift, h]

private def radix4Weights (x : K) : Fin 4 → K :=
  ![1, x, doubledFactor x 1, x * doubledFactor x 1]

/-- Reindex the source evaluator using the exact four-lane natural-basis
identity `naturalLineValue_four_mul_add`. -/
theorem naturalEval_radix4 {n : Nat} (a : Fin (4 * n) → K) (x : K) :
    naturalEval a x =
      ∑ slot : Fin 4,
        radix4Weights x slot *
          naturalEval (laneCoefficients n slot a) (doubledFactor x 2) := by
  unfold naturalEval
  rw [← (fibreIndexEquiv n).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [fibreIndexEquiv_apply, childIndex_val,
    naturalLineValue_four_mul_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro slot _hslot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  change a (childIndex i slot) *
      (naturalLineValue (doubledFactor x 2) i * radix4Weights x slot) =
    radix4Weights x slot *
      (a (childIndex i slot) * naturalLineValue (doubledFactor x 2) i)
  ring

theorem naturalEval_zero {n : Nat} (x : K) :
    naturalEval (fun _ : Fin n => (0 : K)) x = 0 := by
  simp [naturalEval]

/-- The polynomial of the sparse lift evaluates as the original natural-basis
dot product at the twice-doubled point. The polynomial correspondence is a
separate existing bridge theorem. -/
theorem sparseLift_eval {n : Nat} (m : Fin n → K) (x : K) :
    naturalEval (sparseLift m) x = naturalEval m (doubledFactor x 2) := by
  rw [naturalEval_radix4]
  simp_rw [laneCoefficients_sparseLift]
  rw [Fin.sum_univ_four]
  simp [radix4Weights, naturalEval]

/-- The four child points have a common second-doubled parent. -/
def radix4ChildPoint (x0 x1 : K) : Fin 4 → K := ![x0, -x0, x1, -x1]

theorem radix4ChildPoint_t2 (x0 x1 x2 : K)
    (h0 : doubledFactor x0 1 = x2)
    (h1 : doubledFactor x1 1 = -x2) (slot : Fin 4) :
    doubledFactor (radix4ChildPoint x0 x1 slot) 1 = ![x2, x2, -x2, -x2] slot := by
  have h0' : 2 * x0 ^ 2 - 1 = x2 := by
    simpa [doubledFactor] using h0
  have h1' : 2 * x1 ^ 2 - 1 = -x2 := by
    simpa [doubledFactor] using h1
  fin_cases slot <;> simp [radix4ChildPoint, doubledFactor, h0', h1']

theorem radix4ChildPoint_t4 (x0 x1 x2 parent : K)
    (h0 : doubledFactor x0 1 = x2)
    (h1 : doubledFactor x1 1 = -x2)
    (h2 : doubledFactor x2 1 = parent) (slot : Fin 4) :
    doubledFactor (radix4ChildPoint x0 x1 slot) 2 = parent := by
  rw [show 2 = 1 + 1 by omega, doubledFactor_add]
  rw [radix4ChildPoint_t2 x0 x1 x2 h0 h1 slot]
  have h2' : 2 * x2 ^ 2 - 1 = parent := by
    simpa [doubledFactor] using h2
  fin_cases slot <;> simp [doubledFactor, h2']

/-- The sum of the four source-level natural-basis evaluations in a child
fibre is four times the low-lane value at the parent. -/
theorem natural_fibre_sum {n : Nat} (a : Fin (4 * n) → K)
    (x0 x1 x2 parent : K)
    (h0 : doubledFactor x0 1 = x2)
    (h1 : doubledFactor x1 1 = -x2)
    (h2 : doubledFactor x2 1 = parent) :
    (∑ slot : Fin 4,
      naturalEval a (radix4ChildPoint x0 x1 slot)) =
      4 * naturalEval (laneCoefficients n 0 a) parent := by
  have hweight_sum (lane : Fin 4) :
      (∑ slot : Fin 4,
        radix4Weights (radix4ChildPoint x0 x1 slot) lane) =
        (if lane = 0 then (4 : K) else 0) := by
    simp_rw [radix4Weights, radix4ChildPoint_t2 x0 x1 x2 h0 h1]
    fin_cases lane <;>
      simp [Fin.sum_univ_four, radix4ChildPoint]
  simp_rw [naturalEval_radix4]
  simp_rw [radix4ChildPoint_t4 x0 x1 x2 parent h0 h1 h2]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hweight_sum]
  rw [Fin.sum_univ_four]
  simp

/-- The sparse lift of lane zero evaluates at each child as the mean of the
four source-level natural-basis child evaluations. -/
theorem naturalProjection_eval_fibre_mean {n : Nat}
    (h4 : (4 : K) ≠ 0) (a : Fin (4 * n) → K)
    (x0 x1 x2 parent : K)
    (h0 : doubledFactor x0 1 = x2)
    (h1 : doubledFactor x1 1 = -x2)
    (h2 : doubledFactor x2 1 = parent) (slot : Fin 4) :
    naturalEval (sparseLift (laneCoefficients n 0 a))
        (radix4ChildPoint x0 x1 slot) =
      (∑ s : Fin 4,
        naturalEval a (radix4ChildPoint x0 x1 s)) / 4 := by
  calc
    naturalEval (sparseLift (laneCoefficients n 0 a))
        (radix4ChildPoint x0 x1 slot) =
        naturalEval (laneCoefficients n 0 a)
          (doubledFactor (radix4ChildPoint x0 x1 slot) 2) :=
      sparseLift_eval _ _
    _ = naturalEval (laneCoefficients n 0 a) parent := by
      rw [radix4ChildPoint_t4 x0 x1 x2 parent h0 h1 h2]
    _ = (4 * naturalEval (laneCoefficients n 0 a) parent) / 4 := by
      field_simp [h4]
    _ = (∑ s : Fin 4,
        naturalEval a (radix4ChildPoint x0 x1 s)) / 4 := by
      rw [natural_fibre_sum a x0 x1 x2 parent h0 h1 h2]

#print axioms laneCoefficients_sparseLift
#print axioms sparseLift_injective
#print axioms sparseLift_add
#print axioms sparseLift_smul
#print axioms naturalEval_radix4
#print axioms naturalEval_zero
#print axioms sparseLift_eval
#print axioms radix4ChildPoint_t2
#print axioms radix4ChildPoint_t4
#print axioms natural_fibre_sum
#print axioms naturalProjection_eval_fibre_mean

end AspisR1

end
