import AspisV8R16.BalancedTransport
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Source-shaped inverse-dual identity, for arbitrary extracted coefficients.
No honest-generation or balanced-mask premise is permitted here. -/
set_option autoImplicit false
namespace AspisV8R16
open scoped BigOperators
variable {I F : Type*} [Fintype I] [DecidableEq I] [CommRing F]

def transportDual (inactive : Finset I) (pivot : I) (order : I ≃ I)
    (w : I → F) (j : I) : F :=
  if order j ∈ inactive.erase pivot then w (order j) - w pivot else w (order j)

theorem inverseTransport_dot (inactive : Finset I) (pivot : I) (order : I ≃ I)
    (w c : I → F) :
    (∑ r, w r * inverseTransport inactive pivot order c r) =
      ∑ j, transportDual inactive pivot order w j * c j := by
  let u : I → F := fun r => c (order.symm r)
  have hi : inverseTransport inactive pivot order c =
      fun r => u r - if r = pivot then ∑ k ∈ inactive.erase pivot, u k else 0 := by
    funext r
    by_cases h : r = pivot <;> simp [inverseTransport, u, h]
  have hd (r : I) : (if r ∈ inactive.erase pivot then w r - w pivot else w r) =
      w r - if r ∈ inactive.erase pivot then w pivot else 0 := by
    split <;> simp_all
  have hsum : (∑ r, w r * inverseTransport inactive pivot order c r) =
      ∑ r, (if r ∈ inactive.erase pivot then w r - w pivot else w r) * u r := by
    rw [hi]
    simp only [mul_sub, Finset.sum_sub_distrib]
    simp only [hd]
    simp only [sub_mul, Finset.sum_sub_distrib]
    congr 1
    simp only [mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext r; simp
    · intro r hr; rfl
  rw [hsum]
  have hreindex := Equiv.sum_comp order
    (fun r => (if r ∈ inactive.erase pivot then w r - w pivot else w r) * u r)
  simpa [transportDual, u] using hreindex.symm

theorem transportDual_forward_dot (inactive : Finset I) (pivot : I)
    (hp : pivot ∈ inactive) (order : I ≃ I) (w m : I → F) :
    (∑ j, transportDual inactive pivot order w j * transport inactive pivot order m j) =
      ∑ r, w r * m r := by
  rw [← inverseTransport_dot, inverse_transport inactive pivot hp order]

#print axioms inverseTransport_dot
#print axioms transportDual_forward_dot
end AspisV8R16
