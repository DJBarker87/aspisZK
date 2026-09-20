import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Group.Equiv.Defs

/-! Algebra of the R16 balancing row and immutable permutation.
This is a source-shaped model, not a Rust extraction or privacy theorem. -/
set_option autoImplicit false
namespace AspisV8R16
open scoped BigOperators
variable {ι F : Type*} [DecidableEq ι] [AddCommGroup F]

def balance (inactive : Finset ι) (pivot : ι) (u : ι → F) (r : ι) : F :=
  if r = pivot then -(∑ k ∈ inactive.erase pivot, u k) else u r

def transport (inactive : Finset ι) (pivot : ι) (order : ι ≃ ι)
    (m : ι → F) (j : ι) : F :=
  if order j = pivot then ∑ r ∈ inactive, m r else m (order j)

theorem balance_sum_zero (inactive : Finset ι) (pivot : ι)
    (hp : pivot ∈ inactive) (u : ι → F) :
    ∑ r ∈ inactive, balance inactive pivot u r = 0 := by
  rw [← Finset.sum_erase_add _ _ hp]
  have h : ∑ r ∈ inactive.erase pivot, balance inactive pivot u r =
      ∑ r ∈ inactive.erase pivot, u r := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [balance, if_neg (Finset.mem_erase.mp hr).1]
  rw [h]
  simp [balance]

theorem transport_balance (inactive : Finset ι) (pivot : ι)
    (hp : pivot ∈ inactive) (order : ι ≃ ι) (u : ι → F) (j : ι) :
    transport inactive pivot order (balance inactive pivot u) j =
      if order j = pivot then 0 else u (order j) := by
  unfold transport
  rw [balance_sum_zero inactive pivot hp]
  split <;> simp_all [balance]

/-- A coefficient target with zero balancing coordinate has an exact lift.
No new draw of the original mask coins is part of this construction. -/
theorem balanced_target_lift (inactive : Finset ι) (pivot : ι)
    (hp : pivot ∈ inactive) (order : ι ≃ ι) (c : ι → F)
    (hc : c (order.symm pivot) = 0) :
    transport inactive pivot order
      (balance inactive pivot (fun r => c (order.symm r))) = c := by
  funext j
  rw [transport_balance inactive pivot hp]
  by_cases h : order j = pivot
  · have hj : j = order.symm pivot := by rw [← h]; simp
    simp [hj, hc]
  · simp [h]

/-- The balancing operation touches only its pivot and the input support. -/
theorem balance_preserves_zero (inactive : Finset ι) (pivot r : ι)
    (u : ι → F) (hr : r ≠ pivot) (hu : u r = 0) :
    balance inactive pivot u r = 0 := by simp [balance, hr, hu]

def inverseTransport (inactive : Finset ι) (pivot : ι) (order : ι ≃ ι)
    (c : ι → F) (r : ι) : F :=
  if r = pivot then c (order.symm pivot) -
      ∑ k ∈ inactive.erase pivot, c (order.symm k)
  else c (order.symm r)

theorem inverse_transport (inactive : Finset ι) (pivot : ι)
    (hp : pivot ∈ inactive) (order : ι ≃ ι) (m : ι → F) :
    inverseTransport inactive pivot order (transport inactive pivot order m) = m := by
  have hs : ∑ k ∈ inactive.erase pivot,
      transport inactive pivot order m (order.symm k) =
      ∑ k ∈ inactive.erase pivot, m k := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [transport, (Finset.mem_erase.mp hk).1]
  funext r
  by_cases hr : r = pivot
  · subst r
    simp only [inverseTransport, hs]
    simp only [transport, Equiv.apply_symm_apply]
    rw [← Finset.sum_erase_add inactive m hp]
    simp
  · simp [inverseTransport, transport, hr]

theorem transport_injective (inactive : Finset ι) (pivot : ι)
    (hp : pivot ∈ inactive) (order : ι ≃ ι) :
    Function.Injective (transport (F := F) inactive pivot order) := by
  intro m n h
  have hi := congrArg (inverseTransport inactive pivot order) h
  simpa only [inverse_transport inactive pivot hp order] using hi

theorem transport_inverse (inactive : Finset ι) (pivot : ι)
    (hp : pivot ∈ inactive) (order : ι ≃ ι) (c : ι → F) :
    transport inactive pivot order (inverseTransport inactive pivot order c) = c := by
  have hs : ∑ k ∈ inactive.erase pivot, inverseTransport inactive pivot order c k =
      ∑ k ∈ inactive.erase pivot, c (order.symm k) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [inverseTransport, (Finset.mem_erase.mp hk).1]
  funext j
  by_cases hj : order j = pivot
  · simp only [transport, if_pos hj]
    rw [← Finset.sum_erase_add inactive (inverseTransport inactive pivot order c) hp, hs]
    have he : order.symm pivot = j := by rw [← hj]; simp
    simp [inverseTransport, he]
  · simp [transport, inverseTransport, hj]

def transportEquiv (inactive : Finset ι) (pivot : ι)
    (hp : pivot ∈ inactive) (order : ι ≃ ι) : (ι → F) ≃ (ι → F) where
  toFun := transport inactive pivot order
  invFun := inverseTransport inactive pivot order
  left_inv := inverse_transport inactive pivot hp order
  right_inv := transport_inverse inactive pivot hp order

theorem transport_add (inactive : Finset ι) (pivot : ι) (order : ι ≃ ι)
    (m n : ι → F) :
    transport inactive pivot order (m+n) =
      transport inactive pivot order m + transport inactive pivot order n := by
  funext j
  simp only [transport, Pi.add_apply]
  split <;> simp [Finset.sum_add_distrib]

/-- The repaired basis map is additive as well as bijective. This supplies
the model premise for transporting distinct opening functionals. -/
def transportAddEquiv (inactive : Finset ι) (pivot : ι)
    (hp : pivot ∈ inactive) (order : ι ≃ ι) : (ι → F) ≃+ (ι → F) where
  toEquiv := transportEquiv inactive pivot hp order
  map_add' := transport_add inactive pivot order

#print axioms balanced_target_lift
#print axioms balance_sum_zero
#print axioms inverse_transport
#print axioms transport_injective
#print axioms transportEquiv
#print axioms transportAddEquiv
end AspisV8R16
