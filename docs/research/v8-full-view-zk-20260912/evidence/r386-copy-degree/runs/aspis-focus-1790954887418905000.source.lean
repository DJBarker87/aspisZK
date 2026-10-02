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

@[irreducible]
def copyValue (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (s : Fin 4) : F[X] :=
  ∑ r : Fin 1024, rowSelector z j r *
    copyInnerValue tables valueCoeff tag z j s r

@[irreducible]
def copyWeight (weightCoeff : Fin 4 → Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) (s : Fin 4) : F[X] :=
  ∑ r : Fin 1024, rowSelector z j r * C (weightCoeff s r)

@[irreducible]
def copyActive (activeCoeff : Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) : F[X] :=
  ∑ r : Fin 1024, rowSelector z j r * C (activeCoeff r)

def copyDenom (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (chi : Fin 4 → F) (s : Fin 4) : F[X] :=
  C (chi s) - copyValue tables valueCoeff tag z j s

def copyPairDen (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (chi : Fin 4 → F) : F[X] :=
  copyDenom tables valueCoeff tag z j chi 0 * copyDenom tables valueCoeff tag z j chi 1

def copyOtherDen (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F) (tag : Fin 4 → Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) (chi : Fin 4 → F) : F[X] :=
  copyDenom tables valueCoeff tag z j chi 2 * copyDenom tables valueCoeff tag z j chi 3

def copyPairNumerator (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F) (tag : Fin 4 → Fin 1024 → F)
    (weightCoeff : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (chi : Fin 4 → F) : F[X] :=
  copyWeight weightCoeff z j 0 * copyDenom tables valueCoeff tag z j chi 1 +
  copyWeight weightCoeff z j 1 * copyDenom tables valueCoeff tag z j chi 0

def copyOtherNumerator (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F) (tag : Fin 4 → Fin 1024 → F)
    (weightCoeff : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (chi : Fin 4 → F) : F[X] :=
  copyWeight weightCoeff z j 2 * copyDenom tables valueCoeff tag z j chi 3 +
  copyWeight weightCoeff z j 3 * copyDenom tables valueCoeff tag z j chi 2

def copyCore (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (weightCoeff : Fin 4 → Fin 1024 → F)
    (helperTable : Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (chi : Fin 4 → F) : F[X] :=
  copyPairDen tables valueCoeff tag z j chi *
    (claimPolynomial helperTable z j (0 : Fin 3) *
      copyOtherDen tables valueCoeff tag z j chi +
      copyOtherNumerator tables valueCoeff tag weightCoeff z j chi) -
    copyOtherDen tables valueCoeff tag z j chi *
      copyPairNumerator tables valueCoeff tag weightCoeff z j chi

def copyResidual (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (weightCoeff : Fin 4 → Fin 1024 → F)
    (activeCoeff : Fin 1024 → F) (helperTable : Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) (chi : Fin 4 → F) : F[X] :=
  copyActive activeCoeff z j *
    copyCore tables valueCoeff tag weightCoeff helperTable z j chi

theorem mul_degree_bound {p q : F[X]} {a b : Nat}
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p * q).natDegree ≤ a + b := by
  exact natDegree_mul_le.trans (Nat.add_le_add hp hq)

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

theorem copyDenom_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (chi : Fin 4 → F) (s : Fin 4) :
    (copyDenom tables valueCoeff tag z j chi s).natDegree ≤ 2 := by
  unfold copyDenom
  exact sub_bound (by simp) (copyValue_degree tables valueCoeff tag z j s)

theorem copyPairDen_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (chi : Fin 4 → F) :
    (copyPairDen tables valueCoeff tag z j chi).natDegree ≤ 4 := by
  unfold copyPairDen
  exact (mul_degree_bound (copyDenom_degree tables valueCoeff tag z j chi 0)
    (copyDenom_degree tables valueCoeff tag z j chi 1)).trans (by omega)

theorem copyOtherDen_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (chi : Fin 4 → F) :
    (copyOtherDen tables valueCoeff tag z j chi).natDegree ≤ 4 := by
  unfold copyOtherDen
  exact (mul_degree_bound (copyDenom_degree tables valueCoeff tag z j chi 2)
    (copyDenom_degree tables valueCoeff tag z j chi 3)).trans (by omega)

theorem copyPairNumerator_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (weightCoeff : Fin 4 → Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) (chi : Fin 4 → F) :
    (copyPairNumerator tables valueCoeff tag weightCoeff z j chi).natDegree ≤ 3 := by
  unfold copyPairNumerator
  apply natDegree_add_le_of_degree_le
  · exact (mul_degree_bound (copyWeight_degree weightCoeff z j 0)
      (copyDenom_degree tables valueCoeff tag z j chi 1)).trans (by omega)
  · exact (mul_degree_bound (copyWeight_degree weightCoeff z j 1)
      (copyDenom_degree tables valueCoeff tag z j chi 0)).trans (by omega)

theorem copyOtherNumerator_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (weightCoeff : Fin 4 → Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) (chi : Fin 4 → F) :
    (copyOtherNumerator tables valueCoeff tag weightCoeff z j chi).natDegree ≤ 3 := by
  unfold copyOtherNumerator
  apply natDegree_add_le_of_degree_le
  · exact (mul_degree_bound (copyWeight_degree weightCoeff z j 2)
      (copyDenom_degree tables valueCoeff tag z j chi 3)).trans (by omega)
  · exact (mul_degree_bound (copyWeight_degree weightCoeff z j 3)
      (copyDenom_degree tables valueCoeff tag z j chi 2)).trans (by omega)

theorem copyCore_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (weightCoeff : Fin 4 → Fin 1024 → F)
    (helperTable : Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (chi : Fin 4 → F) :
    (copyCore tables valueCoeff tag weightCoeff helperTable z j chi).natDegree ≤ 9 := by
  unfold copyCore
  have hP := copyPairDen_degree tables valueCoeff tag z j chi
  have hN := copyOtherDen_degree tables valueCoeff tag z j chi
  have hH : (claimPolynomial helperTable z j (0 : Fin 3)).natDegree ≤ 1 :=
    simple_claim_degree helperTable z j 0 (by decide)
  have hCn := copyOtherNumerator_degree tables valueCoeff tag weightCoeff z j chi
  have hPn := copyPairNumerator_degree tables valueCoeff tag weightCoeff z j chi
  have hHCn : (claimPolynomial helperTable z j (0 : Fin 3) *
      copyOtherDen tables valueCoeff tag z j chi +
      copyOtherNumerator tables valueCoeff tag weightCoeff z j chi).natDegree ≤ 5 := by
    apply natDegree_add_le_of_degree_le
    · exact (mul_degree_bound hH hN).trans (by omega)
    · exact hCn.trans (by omega)
  have hPHCn : (copyPairDen tables valueCoeff tag z j chi *
      (claimPolynomial helperTable z j (0 : Fin 3) *
        copyOtherDen tables valueCoeff tag z j chi +
        copyOtherNumerator tables valueCoeff tag weightCoeff z j chi)).natDegree ≤ 9 :=
    (mul_degree_bound hP hHCn).trans (by omega)
  have hNPn : (copyOtherDen tables valueCoeff tag z j chi *
      copyPairNumerator tables valueCoeff tag weightCoeff z j chi).natDegree ≤ 7 :=
    (mul_degree_bound hN hPn).trans (by omega)
  have hcore : (copyPairDen tables valueCoeff tag z j chi *
      (claimPolynomial helperTable z j (0 : Fin 3) * copyOtherDen tables valueCoeff tag z j chi +
        copyOtherNumerator tables valueCoeff tag weightCoeff z j chi) -
      copyOtherDen tables valueCoeff tag z j chi *
        copyPairNumerator tables valueCoeff tag weightCoeff z j chi).natDegree ≤ 9 :=
    sub_bound hPHCn (hNPn.trans (by omega))
  exact hcore

theorem copyResidual_degree (tables : Fin 16 → Fin 1024 → F)
    (valueCoeff : Fin 4 → Fin 1024 → Fin 16 → F)
    (tag : Fin 4 → Fin 1024 → F) (weightCoeff : Fin 4 → Fin 1024 → F)
    (activeCoeff : Fin 1024 → F) (helperTable : Fin 1024 → F)
    (z : Fin 10 → F) (j : Fin 10) (chi : Fin 4 → F) :
    (copyResidual tables valueCoeff tag weightCoeff activeCoeff helperTable z j chi).natDegree ≤ 10 := by
  unfold copyResidual
  exact (mul_degree_bound (copyActive_degree activeCoeff z j)
    (copyCore_degree tables valueCoeff tag weightCoeff helperTable z j chi)).trans (by omega)

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
#print axioms copyDenom_degree
#print axioms copyPairDen_degree
#print axioms copyOtherDen_degree
#print axioms copyPairNumerator_degree
#print axioms copyOtherNumerator_degree
#print axioms copyCore_degree
#print axioms copyResidual_degree
#print axioms copyZerocheck_degree
#print axioms copyInactiveHelper_degree
end
end AspisR19.R386CopyDegree
