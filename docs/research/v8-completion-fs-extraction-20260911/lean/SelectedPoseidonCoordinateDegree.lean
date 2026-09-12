import SelectedPoseidonCoordinateSlice

/-! Symbolic coordinate-degree accounting for the projected Poseidon source.

No trace table or 1024-row MLE is unfolded here.  Only the sixteen pointwise
degree hypotheses for each state and the linear selector/opening bounds are
used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 4000

namespace AspisV8Completion.SelectedPoseidonCoordinateDegree
open Polynomial
open AspisV5ComponentCQM31TowerExact
open AspisV8Completion.SelectedPoseidonGenericAlgebra
open AspisV8Completion.SelectedPoseidonCoordinateSlice
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.SelectedInitialOutputsSourcePolynomial
open AspisV8.SelectedSemanticRows

abbrev K := QM31Exact

def Bounded (state : State K[X]) (bound : Nat) : Prop :=
  ∀ lane, (state lane).natDegree ≤ bound

theorem addBound {left right : K[X]} {bound : Nat}
    (hl : left.natDegree ≤ bound) (hr : right.natDegree ≤ bound) :
    (left + right).natDegree ≤ bound :=
  (natDegree_add_le _ _).trans (max_le hl hr)

theorem subBound {left right : K[X]} {bound : Nat}
    (hl : left.natDegree ≤ bound) (hr : right.natDegree ≤ bound) :
    (left - right).natDegree ≤ bound :=
  (natDegree_sub_le _ _).trans (max_le hl hr)

theorem leftConstantBound {constant value : K[X]} {bound : Nat}
    (hc : constant.natDegree = 0) (hv : value.natDegree ≤ bound) :
    (constant * value).natDegree ≤ bound := by
  exact natDegree_mul_le.trans (by omega)

theorem rightConstantBound {value constant : K[X]} {bound : Nat}
    (hv : value.natDegree ≤ bound) (hc : constant.natDegree = 0) :
    (value * constant).natDegree ≤ bound := by
  exact natDegree_mul_le.trans (by omega)

theorem mulBound {left right : K[X]} {leftBound rightBound : Nat}
    (hl : left.natDegree ≤ leftBound) (hr : right.natDegree ≤ rightBound) :
    (left * right).natDegree ≤ leftBound + rightBound :=
  natDegree_mul_le.trans (Nat.add_le_add hl hr)

theorem externalLinear_degree {state : State K[X]} {bound : Nat}
    (bounded : Bounded state bound) : Bounded (externalLinear state) bound := by
  intro lane
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have h0 := natDegree_le_iff_coeff_eq_zero.mp (bounded (0 : Fin 16)) n hn
  have h1 := natDegree_le_iff_coeff_eq_zero.mp (bounded (1 : Fin 16)) n hn
  have h2 := natDegree_le_iff_coeff_eq_zero.mp (bounded (2 : Fin 16)) n hn
  have h3 := natDegree_le_iff_coeff_eq_zero.mp (bounded (3 : Fin 16)) n hn
  have h4 := natDegree_le_iff_coeff_eq_zero.mp (bounded (4 : Fin 16)) n hn
  have h5 := natDegree_le_iff_coeff_eq_zero.mp (bounded (5 : Fin 16)) n hn
  have h6 := natDegree_le_iff_coeff_eq_zero.mp (bounded (6 : Fin 16)) n hn
  have h7 := natDegree_le_iff_coeff_eq_zero.mp (bounded (7 : Fin 16)) n hn
  have h8 := natDegree_le_iff_coeff_eq_zero.mp (bounded (8 : Fin 16)) n hn
  have h9 := natDegree_le_iff_coeff_eq_zero.mp (bounded (9 : Fin 16)) n hn
  have h10 := natDegree_le_iff_coeff_eq_zero.mp (bounded (10 : Fin 16)) n hn
  have h11 := natDegree_le_iff_coeff_eq_zero.mp (bounded (11 : Fin 16)) n hn
  have h12 := natDegree_le_iff_coeff_eq_zero.mp (bounded (12 : Fin 16)) n hn
  have h13 := natDegree_le_iff_coeff_eq_zero.mp (bounded (13 : Fin 16)) n hn
  have h14 := natDegree_le_iff_coeff_eq_zero.mp (bounded (14 : Fin 16)) n hn
  have h15 := natDegree_le_iff_coeff_eq_zero.mp (bounded (15 : Fin 16)) n hn
  fin_cases lane <;> simp [externalLinear, h0, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, h14, h15]

theorem internalLinear_degree {state : State K[X]} {bound : Nat}
    (bounded : Bounded state bound) : Bounded (internalLinear state) bound := by
  intro lane
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have h0 := natDegree_le_iff_coeff_eq_zero.mp (bounded (0 : Fin 16)) n hn
  have h1 := natDegree_le_iff_coeff_eq_zero.mp (bounded (1 : Fin 16)) n hn
  have h2 := natDegree_le_iff_coeff_eq_zero.mp (bounded (2 : Fin 16)) n hn
  have h3 := natDegree_le_iff_coeff_eq_zero.mp (bounded (3 : Fin 16)) n hn
  have h4 := natDegree_le_iff_coeff_eq_zero.mp (bounded (4 : Fin 16)) n hn
  have h5 := natDegree_le_iff_coeff_eq_zero.mp (bounded (5 : Fin 16)) n hn
  have h6 := natDegree_le_iff_coeff_eq_zero.mp (bounded (6 : Fin 16)) n hn
  have h7 := natDegree_le_iff_coeff_eq_zero.mp (bounded (7 : Fin 16)) n hn
  have h8 := natDegree_le_iff_coeff_eq_zero.mp (bounded (8 : Fin 16)) n hn
  have h9 := natDegree_le_iff_coeff_eq_zero.mp (bounded (9 : Fin 16)) n hn
  have h10 := natDegree_le_iff_coeff_eq_zero.mp (bounded (10 : Fin 16)) n hn
  have h11 := natDegree_le_iff_coeff_eq_zero.mp (bounded (11 : Fin 16)) n hn
  have h12 := natDegree_le_iff_coeff_eq_zero.mp (bounded (12 : Fin 16)) n hn
  have h13 := natDegree_le_iff_coeff_eq_zero.mp (bounded (13 : Fin 16)) n hn
  have h14 := natDegree_le_iff_coeff_eq_zero.mp (bounded (14 : Fin 16)) n hn
  have h15 := natDegree_le_iff_coeff_eq_zero.mp (bounded (15 : Fin 16)) n hn
  fin_cases lane <;> simp [internalLinear, h0, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, h14, h15]

set_option maxHeartbeats 20000 in
theorem sumBound {ι : Type*} [Fintype ι] (values : ι → K[X]) {bound : Nat}
    (bounded : ∀ i, (values i).natDegree ≤ bound) :
    (∑ i, values i).natDegree ≤ bound := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact addBound (bounded a) ih

set_option maxHeartbeats 100000

theorem pow5_degree {value : K[X]} {bound : Nat}
    (bounded : value.natDegree ≤ bound) :
    (pow5 value).natDegree ≤ 5 * bound := by
  exact natDegree_pow_le_of_le 5 bounded

theorem fullRound_degree {state constants : State K[X]} {bound : Nat}
    (stateBound : Bounded state bound) (constantBound : Bounded constants bound) :
    Bounded (fullRound state constants) (5 * bound) := by
  apply externalLinear_degree
  intro lane
  exact pow5_degree (addBound (stateBound lane) (constantBound lane))

theorem internalRound_degree {state : State K[X]} {constant : K[X]} {bound : Nat}
    (stateBound : Bounded state bound) (constantBound : constant.natDegree ≤ bound) :
    Bounded (internalRound state constant) (5 * bound) := by
  apply internalLinear_degree
  intro lane
  simp only [internalRound]
  split
  · exact pow5_degree (addBound (stateBound lane) constantBound)
  · exact (stateBound lane).trans (by omega)

theorem absorbRate_degree {z xor12 : State K[X]} {bound : Nat}
    (zBound : Bounded z bound) (xorBound : Bounded xor12 bound) :
    Bounded (absorbRate z xor12) bound := by
  intro lane
  simp only [absorbRate]
  split
  · exact addBound (zBound lane) (xorBound lane)
  · exact zBound lane

theorem embeddedConstant_degree (value : F) :
    (baseToPolynomial value).natDegree ≤ 0 := by simp [baseToPolynomial]

theorem embeddedConstant_natDegree (value : F) :
    (baseToPolynomial value).natDegree = 0 :=
  Nat.le_zero.mp (embeddedConstant_degree value)

theorem fullEvenConstants_degree (rc : RC) {selector : State K[X]}
    (bounded : Bounded selector 1) :
    Bounded (fullEvenConstants baseToPolynomial rc selector) 1 := by
  intro lane
  unfold fullEvenConstants
  have h1 : (selector 1 * baseToPolynomial (rc.extInit 2 lane)).natDegree ≤ 1 :=
    (mulBound (bounded 1) (embeddedConstant_degree (rc.extInit 2 lane))).trans (by omega)
  have h9 : (selector 9 * baseToPolynomial (rc.extFinal 0 lane)).natDegree ≤ 1 :=
    (mulBound (bounded 9) (embeddedConstant_degree (rc.extFinal 0 lane))).trans (by omega)
  have h10 : (selector 10 * baseToPolynomial (rc.extFinal 2 lane)).natDegree ≤ 1 :=
    (mulBound (bounded 10) (embeddedConstant_degree (rc.extFinal 2 lane))).trans (by omega)
  exact addBound (addBound h1 h9) h10

theorem fullOddConstants_degree (rc : RC) {selector : State K[X]}
    (bounded : Bounded selector 1) :
    Bounded (fullOddConstants baseToPolynomial rc selector) 1 := by
  intro lane
  unfold fullOddConstants
  have h1 : (selector 1 * baseToPolynomial (rc.extInit 3 lane)).natDegree ≤ 1 :=
    (mulBound (bounded 1) (embeddedConstant_degree (rc.extInit 3 lane))).trans (by omega)
  have h9 : (selector 9 * baseToPolynomial (rc.extFinal 1 lane)).natDegree ≤ 1 :=
    (mulBound (bounded 9) (embeddedConstant_degree (rc.extFinal 1 lane))).trans (by omega)
  have h10 : (selector 10 * baseToPolynomial (rc.extFinal 3 lane)).natDegree ≤ 1 :=
    (mulBound (bounded 10) (embeddedConstant_degree (rc.extFinal 3 lane))).trans (by omega)
  exact addBound (addBound h1 h9) h10

theorem internalEvenConstant_degree (rc : RC) {selector : State K[X]}
    (bounded : Bounded selector 1) :
    (internalEvenConstant baseToPolynomial rc selector).natDegree ≤ 1 := by
  unfold internalEvenConstant
  apply sumBound
  intro row
  exact (mulBound (bounded ⟨row.val + 2, by omega⟩)
    (embeddedConstant_degree _)).trans (by omega)

theorem internalOddConstant_degree (rc : RC) {selector : State K[X]}
    (bounded : Bounded selector 1) :
    (internalOddConstant baseToPolynomial rc selector).natDegree ≤ 1 := by
  unfold internalOddConstant
  apply sumBound
  intro row
  exact (mulBound (bounded ⟨row.val + 2, by omega⟩)
    (embeddedConstant_degree _)).trans (by omega)

theorem selectorSlice_degree (fixed : Fin 10 → K) (round : Fin 10) :
    Bounded (selectorSlice fixed round) 1 := fun index => mleSlice_degree _ _ _

theorem traceSlice_degree (table : BaseTable) (view : Fin 3)
    (fixed : Fin 10 → K) (round : Fin 10) :
    Bounded (traceSlice table view fixed round) 1 :=
  fun lane => openingSlice_degree _ _ _

theorem leadingPrediction_degree (rc : RC) {z xor12 : State K[X]}
    (zBound : Bounded z 1) (xorBound : Bounded xor12 1) :
    Bounded (leadingPrediction baseToPolynomial rc z xor12) 25 := by
  unfold leadingPrediction
  have inner : Bounded
      (fullRound (externalLinear (absorbRate z xor12))
        (fun lane => baseToPolynomial (rc.extInit 0 lane))) 5 := by
    have constants : Bounded (fun lane => baseToPolynomial (rc.extInit 0 lane)) 1 :=
      fun lane => (embeddedConstant_degree _).trans (by omega)
    have raw := fullRound_degree
      (externalLinear_degree (absorbRate_degree zBound xorBound))
      constants
    simpa using raw
  exact fullRound_degree inner
    (fun lane => (embeddedConstant_degree _).trans (by omega))

theorem fullPrediction_degree (rc : RC) {z selector : State K[X]}
    (zBound : Bounded z 1) (selectorBound : Bounded selector 1) :
    Bounded (fullPrediction baseToPolynomial rc z selector) 25 := by
  unfold fullPrediction
  exact fullRound_degree
    (fullRound_degree zBound (fullEvenConstants_degree rc selectorBound))
    (fun lane => (fullOddConstants_degree rc selectorBound lane).trans (by omega))

theorem internalPrediction_degree (rc : RC) {z selector : State K[X]}
    (zBound : Bounded z 1) (selectorBound : Bounded selector 1) :
    Bounded (internalPrediction baseToPolynomial rc z selector) 25 := by
  unfold internalPrediction
  exact internalRound_degree
    (internalRound_degree zBound (internalEvenConstant_degree rc selectorBound))
    ((internalOddConstant_degree rc selectorBound).trans (by omega))

theorem weight_degree {selector : State K[X]} (bounded : Bounded selector 1) :
    (leadingWeight selector).natDegree ≤ 1 ∧
      (fullWeight selector).natDegree ≤ 1 ∧
      (internalWeight selector).natDegree ≤ 1 := by
  refine ⟨bounded 0, addBound (addBound (bounded 1) (bounded 9)) (bounded 10), ?_⟩
  unfold internalWeight
  exact sumBound _ fun row => bounded ⟨row.val + 2, by omega⟩

theorem weightedResidual_degree (block : K[X])
    (selector successor leading full internal : State K[X]) (lane : Fin 16)
    (blockBound : block.natDegree ≤ 1) (selectorBound : Bounded selector 1)
    (successorBound : Bounded successor 1) (leadingBound : Bounded leading 25)
    (fullBound : Bounded full 25) (internalBound : Bounded internal 25) :
    (block *
      (leadingWeight selector * (successor lane - leading lane) +
        fullWeight selector * (successor lane - full lane) +
        internalWeight selector * (successor lane - internal lane))).natDegree ≤ 27 := by
  have hs := selectorBound
  have hn := successorBound
  have weights := weight_degree hs
  let a := leadingWeight selector *
    (successor lane - leading lane)
  let b := fullWeight selector *
    (successor lane - full lane)
  let c := internalWeight selector *
    (successor lane - internal lane)
  have ha : a.natDegree ≤ 26 :=
    (mulBound weights.1 (subBound ((hn lane).trans (by omega)) (leadingBound lane))).trans (by omega)
  have hb : b.natDegree ≤ 26 :=
    (mulBound weights.2.1 (subBound ((hn lane).trans (by omega)) (fullBound lane))).trans (by omega)
  have hc : c.natDegree ≤ 26 :=
    (mulBound weights.2.2 (subBound ((hn lane).trans (by omega)) (internalBound lane))).trans (by omega)
  change (block * (a + b + c)).natDegree ≤ 27
  exact (mulBound blockBound (addBound (addBound ha hb) hc)).trans (by omega)

#print axioms externalLinear_degree
#print axioms internalLinear_degree
#print axioms weightedResidual_degree
end AspisV8Completion.SelectedPoseidonCoordinateDegree
