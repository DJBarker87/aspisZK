import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Abel

set_option autoImplicit false
namespace AspisV8R10
variable {K U V : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]

noncomputable def kernelToFiber (A : U →ₗ[K] V) (u0 : U) :
    {u : U // A u = 0} ≃ {u : U // A u = A u0} where
  toFun u := ⟨u0 + u.1, by simp [map_add, u.2]⟩
  invFun u := ⟨u.1 - u0, by simp [map_sub, u.2]⟩
  left_inv u := by
    apply Subtype.ext
    change (u0 + u.1) - u0 = u.1
    abel
  right_inv u := by
    apply Subtype.ext
    change u0 + (u.1 - u0) = u.1
    abel

theorem affine_fiber_card [Fintype U] (A : U →ₗ[K] V) (u0 : U) :
    Nat.card {u : U // A u = 0} = Nat.card {u : U // A u = A u0} :=
  Nat.card_congr (kernelToFiber A u0)

def additiveCoinTransport (s : U) : U ≃ U where
  toFun u := u + s
  invFun u := u - s
  left_inv u := by
    simp only [sub_eq_add_neg]
    abel
  right_inv u := by
    simp only [sub_eq_add_neg]
    abel

#print axioms affine_fiber_card
#print axioms additiveCoinTransport
end AspisV8R10
