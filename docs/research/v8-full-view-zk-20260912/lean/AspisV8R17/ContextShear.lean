import AspisV8H1C2.FiniteTransport
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Abel

/-! Different hidden C1 contexts may change H1's semantic contribution.
This finite bijection does not require the two shared-message maps to be
identical. Required correction equations remain explicit source gates. -/
set_option autoImplicit false
namespace AspisV8R17
variable {H G A B S : Type*}
  [AddCommGroup H] [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup S]

def contextShear (dh : H) (dg : H → G) : H × G ≃ H × G where
  toFun x := (x.1 + dh, x.2 + dg x.1)
  invFun y := (y.1 - dh, y.2 - dg (y.1 - dh))
  left_inv x := by rcases x with ⟨h,g⟩; simp
  right_inv y := by rcases y with ⟨h,g⟩; simp

def contextObservation (hv : H →+ A) (gv : G →+ B) (gs : G →+ S)
    (hs : H → S) (offset : A × B × S) (x : H × G) : A × B × S :=
  (hv x.1, gv x.2, hs x.1 + gs x.2) + offset

theorem context_shear_commutes
    (hv : H →+ A) (gv : G →+ B) (gs : G →+ S)
    (left right : H → S) (a b : A × B × S) (dh : H) (dg : H → G)
    (hh : hv dh = a.1 - b.1)
    (hg : ∀ h, gv (dg h) = a.2.1 - b.2.1)
    (hs : ∀ h, gs (dg h) = left h - right (h + dh) + (a.2.2 - b.2.2))
    (x : H × G) :
    contextObservation hv gv gs right b (contextShear dh dg x) =
      contextObservation hv gv gs left a x := by
  rcases x with ⟨h,g⟩
  apply Prod.ext
  · change hv (h + dh) + b.1 = hv h + a.1
    rw [map_add, hh]
    abel
  · apply Prod.ext
    · change gv (g + dg h) + b.2.1 = gv g + a.2.1
      rw [map_add, hg]
      abel
    · change right (h + dh) + gs (g + dg h) + b.2.2 = left h + gs g + a.2.2
      rw [map_add, hs]
      abel

theorem context_shear_same_uniform_law [Fintype H] [Fintype G]
    (hv : H →+ A) (gv : G →+ B) (gs : G →+ S)
    (left right : H → S) (a b : A × B × S) (dh : H) (dg : H → G)
    (hh : hv dh = a.1 - b.1)
    (hg : ∀ h, gv (dg h) = a.2.1 - b.2.1)
    (hs : ∀ h, gs (dg h) = left h - right (h + dh) + (a.2.2 - b.2.2)) :
    AspisV8H1C2.SameUniformLaw (contextObservation hv gv gs left a)
      (contextObservation hv gv gs right b) := by
  exact AspisV8H1C2.sameUniformLaw_of_equiv _ _ (contextShear dh dg)
    (context_shear_commutes hv gv gs left right a b dh dg hh hg hs)

#print axioms contextShear
#print axioms context_shear_commutes
#print axioms context_shear_same_uniform_law
end AspisV8R17
