import AspisV8R19.R381ProjectedPoseidonDegree
import AspisV8R19.R376SimplePointDegree
import AspisV8R19.R377SelectorCoordinateDegree

/-! Exact-field polynomial degree model for the scalar Copy residual. The
source selector/value/weight gathers and their word-level execution remain
separate obligations. -/
set_option autoImplicit false
namespace AspisR19.R386CopyDegree
open Polynomial R374SingleCoordinateDegree R376SimplePointDegree
open AspisV8R19.R377SelectorCoordinateDegree
open AspisR19.R381ProjectedPoseidonDegree
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

def rowBits (r : Fin 1024) (i : Fin 10) : Bool :=
  decide ((r.val / 2 ^ (9 - i.val)) % 2 = 1)

def rowSelector (z : Fin 10 → F) (j : Fin 10) (r : Fin 1024) : F[X] :=
  selectorPolynomial Finset.univ (rowBits r) z j

def copyInnerValue (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (s : Fin 4) (r : Fin 1024) : F[X] :=
  C (tag s r) + ∑ c : Fin 16,
    C (valueCoeff s r c) * claimPolynomial (tables c) z j (0 : Fin 3)

def copyValue (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (s : Fin 4) : F[X] :=
  ∑ r : Fin 1024, rowSelector z j r *
    copyInnerValue tables valueCoeff tag z j s r

def copyWeight (weightCoeff : Fin 4 → Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) (s : Fin 4) : F[X] :=
  ∑ r : Fin 1024, rowSelector z j r * C (weightCoeff s r)

def copyActive (activeCoeff : Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) : F[X] :=
  ∑ r : Fin 1024, rowSelector z j r * C (activeCoeff r)

theorem rowSelector_degree (z : Fin 10 → F) (j : Fin 10) (r : Fin 1024) :
    (rowSelector z j r).natDegree ≤ 1 := by
  exact (selectorPolynomial_degree Finset.univ (rowBits r) z j).trans (by simp)

theorem copyInnerValue_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (s : Fin 4) (r : Fin 1024) :
    (copyInnerValue tables valueCoeff tag z j s r).natDegree ≤ 1 := by
  unfold copyInnerValue
  have hsum : (∑ c : Fin 16,
      C (valueCoeff s r c) * claimPolynomial (tables c) z j (0 : Fin 3)).natDegree ≤ 1 := by
    apply natDegree_sum_le_of_forall_le
    intro c hc
    apply natDegree_mul_le.trans
    simpa only [natDegree_C, zero_add] using simple_claim_degree (tables c) z j 0 (by decide)
  exact natDegree_add_le_of_degree_le (by simp) hsum

theorem copyValue_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (s : Fin 4) :
    (copyValue tables valueCoeff tag z j s).natDegree ≤ 2 := by
  unfold copyValue
  apply natDegree_sum_le_of_forall_le
  intro r hr
  calc
    _ ≤ (rowSelector z j r).natDegree +
        (copyInnerValue tables valueCoeff tag z j s r).natDegree := natDegree_mul_le
    _ ≤ 1 + 1 := Nat.add_le_add (rowSelector_degree z j r)
        (copyInnerValue_degree tables valueCoeff tag z j s r)
    _ = 2 := by norm_num

theorem copyWeight_degree (weightCoeff : Fin 4 → Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) (s : Fin 4) :
    (copyWeight weightCoeff z j s).natDegree ≤ 1 := by
  unfold copyWeight
  apply natDegree_sum_le_of_forall_le
  intro r hr
  apply natDegree_mul_le.trans
  simpa only [natDegree_C, add_zero] using rowSelector_degree z j r

theorem copyActive_degree (activeCoeff : Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) :
    (copyActive activeCoeff z j).natDegree ≤ 1 := by
  unfold copyActive
  apply natDegree_sum_le_of_forall_le
  intro r hr
  apply natDegree_mul_le.trans
  simpa only [natDegree_C, add_zero] using rowSelector_degree z j r

theorem mul_degree_bound {p q : F[X]} {a b : Nat}
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p * q).natDegree ≤ a + b := by
  exact natDegree_mul_le.trans (Nat.add_le_add hp hq)

/- Generic last-stage algebra: only the already-derived degrees of the
four denominators, four weights, active selector, and helper are consumed. -/
def genericDenom (v : Fin 4 → F[X]) (chi : Fin 4 → F) (s : Fin 4) : F[X] :=
  C (chi s) - v s

def genericPairDen (v : Fin 4 → F[X]) (chi : Fin 4 → F) : F[X] :=
  genericDenom v chi 0 * genericDenom v chi 1

def genericOtherDen (v : Fin 4 → F[X]) (chi : Fin 4 → F) : F[X] :=
  genericDenom v chi 2 * genericDenom v chi 3

def genericPairNumerator (v w : Fin 4 → F[X]) (chi : Fin 4 → F) : F[X] :=
  w 0 * genericDenom v chi 1 + w 1 * genericDenom v chi 0

def genericOtherNumerator (v w : Fin 4 → F[X]) (chi : Fin 4 → F) : F[X] :=
  w 2 * genericDenom v chi 3 + w 3 * genericDenom v chi 2

def genericCopyCore (v w : Fin 4 → F[X]) (helper : F[X]) (chi : Fin 4 → F) : F[X] :=
  genericPairDen v chi * (helper * genericOtherDen v chi + genericOtherNumerator v w chi) -
    genericOtherDen v chi * genericPairNumerator v w chi

def genericCopyResidual (v w : Fin 4 → F[X]) (active helper : F[X])
    (chi : Fin 4 → F) : F[X] :=
  active * genericCopyCore v w helper chi

theorem genericDenom_degree (v : Fin 4 → F[X]) (chi : Fin 4 → F)
    (hv : ∀ s, (v s).natDegree ≤ 2) (s : Fin 4) :
    (genericDenom v chi s).natDegree ≤ 2 := by
  unfold genericDenom
  exact sub_bound (by simp) (hv s)

theorem genericPairDen_degree (v : Fin 4 → F[X]) (chi : Fin 4 → F)
    (hv : ∀ s, (v s).natDegree ≤ 2) :
    (genericPairDen v chi).natDegree ≤ 4 := by
  unfold genericPairDen
  exact (mul_degree_bound (genericDenom_degree v chi hv 0)
    (genericDenom_degree v chi hv 1)).trans (by omega)

theorem genericOtherDen_degree (v : Fin 4 → F[X]) (chi : Fin 4 → F)
    (hv : ∀ s, (v s).natDegree ≤ 2) :
    (genericOtherDen v chi).natDegree ≤ 4 := by
  unfold genericOtherDen
  exact (mul_degree_bound (genericDenom_degree v chi hv 2)
    (genericDenom_degree v chi hv 3)).trans (by omega)

theorem genericPairNumerator_degree (v w : Fin 4 → F[X]) (chi : Fin 4 → F)
    (hv : ∀ s, (v s).natDegree ≤ 2) (hw : ∀ s, (w s).natDegree ≤ 1) :
    (genericPairNumerator v w chi).natDegree ≤ 3 := by
  unfold genericPairNumerator
  apply natDegree_add_le_of_degree_le
  · exact (mul_degree_bound (hw 0) (genericDenom_degree v chi hv 1)).trans (by omega)
  · exact (mul_degree_bound (hw 1) (genericDenom_degree v chi hv 0)).trans (by omega)

theorem genericOtherNumerator_degree (v w : Fin 4 → F[X]) (chi : Fin 4 → F)
    (hv : ∀ s, (v s).natDegree ≤ 2) (hw : ∀ s, (w s).natDegree ≤ 1) :
    (genericOtherNumerator v w chi).natDegree ≤ 3 := by
  unfold genericOtherNumerator
  apply natDegree_add_le_of_degree_le
  · exact (mul_degree_bound (hw 2) (genericDenom_degree v chi hv 3)).trans (by omega)
  · exact (mul_degree_bound (hw 3) (genericDenom_degree v chi hv 2)).trans (by omega)

theorem genericCopyCore_degree (v w : Fin 4 → F[X]) (helper : F[X])
    (chi : Fin 4 → F) (hv : ∀ s, (v s).natDegree ≤ 2)
    (hw : ∀ s, (w s).natDegree ≤ 1) (hh : helper.natDegree ≤ 1) :
    (genericCopyCore v w helper chi).natDegree ≤ 9 := by
  unfold genericCopyCore
  have hP := genericPairDen_degree v chi hv
  have hN := genericOtherDen_degree v chi hv
  have hcn := genericOtherNumerator_degree v w chi hv hw
  have hpn := genericPairNumerator_degree v w chi hv hw
  have hsum : (helper * genericOtherDen v chi + genericOtherNumerator v w chi).natDegree ≤ 5 := by
    apply natDegree_add_le_of_degree_le
    · exact (mul_degree_bound hh hN).trans (by omega)
    · exact hcn.trans (by omega)
  have hleft : (genericPairDen v chi *
      (helper * genericOtherDen v chi + genericOtherNumerator v w chi)).natDegree ≤ 9 :=
    (mul_degree_bound hP hsum).trans (by omega)
  have hright : (genericOtherDen v chi * genericPairNumerator v w chi).natDegree ≤ 7 :=
    (mul_degree_bound hN hpn).trans (by omega)
  exact sub_bound hleft (hright.trans (by omega))

theorem genericCopyResidual_degree (v w : Fin 4 → F[X]) (active helper : F[X])
    (chi : Fin 4 → F) (hv : ∀ s, (v s).natDegree ≤ 2)
    (hw : ∀ s, (w s).natDegree ≤ 1) (ha : active.natDegree ≤ 1)
    (hh : helper.natDegree ≤ 1) :
    (genericCopyResidual v w active helper chi).natDegree ≤ 10 := by
  unfold genericCopyResidual
  exact (mul_degree_bound ha (genericCopyCore_degree v w helper chi hv hw hh)).trans (by omega)

def copyResidual (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (weightCoeff : Fin 4 → Fin 1024 → F)
    (activeCoeff : Fin 1024 → F) (helperTable : Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) (chi : Fin 4 → F) : F[X] :=
  genericCopyResidual (copyValue tables valueCoeff tag z j)
    (copyWeight weightCoeff z j) (copyActive activeCoeff z j)
    (claimPolynomial helperTable z j (0 : Fin 3)) chi

theorem copyResidual_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (weightCoeff : Fin 4 → Fin 1024 → F)
    (activeCoeff : Fin 1024 → F) (helperTable : Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) (chi : Fin 4 → F) :
    (copyResidual tables valueCoeff tag weightCoeff activeCoeff helperTable z j chi).natDegree ≤ 10 := by
  unfold copyResidual
  apply genericCopyResidual_degree
  · intro s
    exact copyValue_degree tables valueCoeff tag z j s
  · intro s
    exact copyWeight_degree weightCoeff z j s
  · exact copyActive_degree activeCoeff z j
  · exact simple_claim_degree helperTable z j 0 (by decide)

theorem copyZerocheck_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (weightCoeff : Fin 4 → Fin 1024 → F)
    (activeCoeff : Fin 1024 → F) (helperTable : Fin 1024 → F)
    (z zc : Fin 10 → F) (j : Fin 10) (chi : Fin 4 → F) :
    (equality z zc j *
      copyResidual tables valueCoeff tag weightCoeff activeCoeff helperTable z j chi).natDegree ≤ 11 := by
  exact natDegree_mul_le.trans (Nat.add_le_add (equality_degree z zc j)
    (copyResidual_degree tables valueCoeff tag weightCoeff activeCoeff helperTable z j chi))

theorem copyInactiveHelper_degree (activeCoeff : Fin 1024 → F)
    (helperTable : Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10) :
    ((1 - copyActive activeCoeff z j) * claimPolynomial helperTable z j (0 : Fin 3)).natDegree ≤ 2 := by
  have ha : (1 - copyActive activeCoeff z j).natDegree ≤ 1 :=
    sub_bound (by simp) (copyActive_degree activeCoeff z j)
  have hh : (claimPolynomial helperTable z j (0 : Fin 3)).natDegree ≤ 1 :=
    simple_claim_degree helperTable z j 0 (by decide)
  exact natDegree_mul_le.trans (Nat.add_le_add ha hh)

#print axioms rowSelector_degree
#print axioms copyInnerValue_degree
#print axioms copyValue_degree
#print axioms copyWeight_degree
#print axioms copyActive_degree
#print axioms genericDenom_degree
#print axioms genericPairDen_degree
#print axioms genericOtherDen_degree
#print axioms genericPairNumerator_degree
#print axioms genericOtherNumerator_degree
#print axioms genericCopyCore_degree
#print axioms genericCopyResidual_degree
#print axioms copyResidual_degree
#print axioms copyZerocheck_degree
#print axioms copyInactiveHelper_degree
end
end AspisR19.R386CopyDegree
