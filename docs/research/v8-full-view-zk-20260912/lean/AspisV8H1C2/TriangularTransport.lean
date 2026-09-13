import AspisV8H1C2.NonlinearFreshPad
import Mathlib.Data.Fintype.Prod

/-! The shift may depend on old coins, but not on the fresh padding coin.
Earlier observation equality is an explicit premise of this transport. -/
set_option autoImplicit false
namespace AspisV8H1C2
noncomputable section
variable {R S U H V : Type*} [AddCommGroup U]

def triangularTransport (e : R ≃ S) (shift : R → U) : (R × U) ≃ (S × U) where
  toFun x := (e x.1, x.2 + shift x.1)
  invFun x := (e.symm x.1, x.2 - shift (e.symm x.1))
  left_inv x := by rcases x with ⟨r,u⟩; simp
  right_inv x := by rcases x with ⟨s,u⟩; simp

theorem triangular_view_transport
    [Fintype R] [Fintype S] [Fintype U] [Nonempty R] [Nonempty S]
    (e : R ≃ S) (shift : R → U)
    (oldPrefix : R → H) (newPrefix : S → H)
    (oldNext : R → U → V) (newNext : S → U → V)
    (prefixExact : ∀ r, newPrefix (e r) = oldPrefix r)
    (nextExact : ∀ r u, newNext (e r) (u + shift r) = oldNext r u) :
    SameUniformLaw (fun x : R × U => (oldPrefix x.1, oldNext x.1 x.2))
      (fun x : S × U => (newPrefix x.1, newNext x.1 x.2)) := by
  apply sameUniformLaw_of_equiv _ _ (triangularTransport e shift)
  rintro ⟨r,u⟩
  exact Prod.ext (prefixExact r) (nextExact r u)

#print axioms triangular_view_transport
end
end AspisV8H1C2
