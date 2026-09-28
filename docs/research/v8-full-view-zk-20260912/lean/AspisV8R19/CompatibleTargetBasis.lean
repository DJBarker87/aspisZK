/- Basis of the kernel of one nonzero coordinate covector. Used for the
   271 semantic coordinates and seven cross-polynomial coefficients. -/
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace AspisR19.CompatibleTargetBasis
variable {F I : Type*} [Field F] [Fintype I] [DecidableEq I]

def basis (e : I → F) (p i j : I) : F :=
  (if j=i then 1 else 0) - e i/e p*(if j=p then 1 else 0)

theorem pivot_zero (e : I → F) (p : I) (hp : e p ≠ 0) :
    ∀ j, basis e p p j=0 := by
  intro j
  simp [basis,hp]

theorem basis_compatible (e : I → F) (p i : I) (hp : e p ≠ 0) :
    ∑ j, e j*basis e p i j=0 := by
  have hfirst : (∑ j, e j*(if j=i then 1 else 0))=e i := by
    simp [mul_ite]
  have hsecond : (∑ j, e j*(e i/e p*(if j=p then 1 else 0))) = e p*(e i/e p) := by
    simp [mul_ite]
  simp only [basis,mul_sub,Finset.sum_sub_distrib]
  rw [hfirst,hsecond]
  rw [mul_comm (e p), div_mul_cancel₀ _ hp,sub_self]

theorem compatible_decomposition (e t : I → F) (p : I)
    (ht : ∑ i, t i*e i=0) :
    ∀ j, (∑ i, t i*basis e p i j)=t j := by
  intro j
  have hfirst : (∑ i, t i*(if j=i then 1 else 0))=t j := by
    simp [mul_ite]
  have hsecond : (∑ i, t i*(e i/e p*(if j=p then 1 else 0))) =
      ((∑ i, t i*e i)/e p)*(if j=p then 1 else 0) := by
    simp only [div_eq_mul_inv, ← mul_assoc, Finset.sum_mul]
  simp only [basis,mul_sub,Finset.sum_sub_distrib]
  rw [hfirst,hsecond,ht]
  simp

#print axioms pivot_zero
#print axioms basis_compatible
#print axioms compatible_decomposition
end AspisR19.CompatibleTargetBasis
