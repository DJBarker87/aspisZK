import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic.Abel
import AspisV8R16.BalancedTransport

/-! Correct two-functional algebra. It does not provide commitment
extraction, Fiat--Shamir soundness, or a source refinement of T and L. -/
set_option autoImplicit false
namespace AspisV8R17
variable {V F : Type*} [AddCommGroup V] [AddCommGroup F]

def quotientFunctional (T : V ≃+ V) (L : V →+ V) (w : V →+ F) : V →+ F :=
  w.comp (T.symm.toAddMonoidHom.comp L)

/-- Unlike a single combined input, two channels retain the distinction
between the ordinary-column and G-specific functionals. -/
theorem two_channel_opening_identity (T : V ≃+ V) (L : V →+ V)
    (u v : V →+ F) (qR qG iR iG : V) :
    u (T.symm (iR + L qR)) + v (T.symm (iG + L qG)) -
      u (T.symm iR) - v (T.symm iG) =
      quotientFunctional T L u qR + quotientFunctional T L v qG := by
  simp only [quotientFunctional, AddMonoidHom.comp_apply, map_add,
    AddEquiv.toAddMonoidHom_eq_coe]
  abel

/-- Instantiate the transform with the proved R16 balancing/permutation
map, rather than assuming that this particular map is additive. -/
theorem balanced_two_channel_opening_identity {ι A B : Type*} [DecidableEq ι]
    [AddCommGroup A] [AddCommGroup B] (inactive : Finset ι) (pivot : ι)
    (hp : pivot ∈ inactive) (order : ι ≃ ι) (L : (ι → A) →+ (ι → A))
    (u v : (ι → A) →+ B) (qR qG iR iG : ι → A) :
    let T := AspisV8R16.transportAddEquiv inactive pivot hp order
    u (T.symm (iR + L qR)) + v (T.symm (iG + L qG)) -
      u (T.symm iR) - v (T.symm iG) =
      quotientFunctional T L u qR + quotientFunctional T L v qG := by
  exact two_channel_opening_identity
    (AspisV8R16.transportAddEquiv inactive pivot hp order) L u v qR qG iR iG

#print axioms two_channel_opening_identity
#print axioms balanced_two_channel_opening_identity
end AspisV8R17
