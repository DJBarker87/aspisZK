import AspisV8H1C2.FiniteTransport
import AspisV8R17.CompatibleGluing
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic.Abel

/-! Finite counting for a FIXED additive observation map. The source coin
law, affine source representation and existence of the required correction
must be supplied separately. No adaptive conditioning is assumed away. -/
set_option autoImplicit false
namespace AspisV8R17
variable {C V : Type*} [AddCommGroup C] [AddCommGroup V]

def coinTranslation (delta : C) : C ≃ C where
  toFun x := x + delta
  invFun x := x - delta
  left_inv x := by simp
  right_inv x := by simp

theorem affine_translation_commutes (f : C →+ V) (a b : V) (delta : C)
    (correction : f delta = a - b) (x : C) :
    f (coinTranslation delta x) + b = f x + a := by
  change f (x + delta) + b = f x + a
  rw [map_add, correction]
  abel

/-- All already-observed coordinates represented by f are retained at once.
This translates the existing coins; it does not resample a used mask. -/
def affinePosteriorEquiv (f : C →+ V) (a b : V) (delta : C)
    (correction : f delta = a - b) (view : V) :
    {x : C // f x + a = view} ≃ {x : C // f x + b = view} :=
  AspisV8H1C2.observationFiberEquiv (fun x => f x + a) (fun x => f x + b)
    (coinTranslation delta) (affine_translation_commutes f a b delta correction) view

theorem affine_fiber_counts [Fintype C] (f : C →+ V) (a b : V) (delta : C)
    (correction : f delta = a - b) (view : V) :
    AspisV8H1C2.fiberCount (fun x => f x + a) view =
      AspisV8H1C2.fiberCount (fun x => f x + b) view := by
  classical
  exact Fintype.card_congr (affinePosteriorEquiv f a b delta correction view)

theorem affine_same_uniform_law [Fintype C] (f : C →+ V) (a b : V)
    (delta : C) (correction : f delta = a - b) :
    AspisV8H1C2.SameUniformLaw (fun x => f x + a) (fun x => f x + b) := by
  exact AspisV8H1C2.sameUniformLaw_of_equiv _ _ (coinTranslation delta)
    (affine_translation_commutes f a b delta correction)

section Joint
variable {H G A B S E : Type*}
  [AddCommGroup H] [AddCommGroup G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup S] [AddCommGroup E]

def jointObservation (hv : H →+ A) (gv : G →+ B)
    (hs : H →+ S) (gs : G →+ S) : H × G →+ A × B × S where
  toFun x := (hv x.1, gv x.2, hs x.1 + gs x.2)
  map_zero' := by simp
  map_add' x y := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · simp only [Prod.snd_add, Prod.fst_add, map_add]
        abel

/-- Compose coverage with counting, but only after requiring additive
source maps and compatible witness offsets. Those stronger premises are
what distinguish this result from an existence-only gluing statement. -/
theorem joint_affine_same_uniform_law [Fintype H] [Fintype G]
    (hv : H →+ A) (gv : G →+ B) (hs : H →+ S) (gs : G →+ S)
    (allowedH : A → Prop) (allowedG : B → Prop)
    (check : S →+ E) (hCheck : A → E) (gCheck : B → E)
    (hCoverage : ∀ a, allowedH a → ∃ h, hv h = a)
    (hConsistency : ∀ h, check (hs h) = hCheck (hv h))
    (gCoverage : ∀ b s, allowedG b → check s = gCheck b →
      ∃ g, gv g = b ∧ gs g = s)
    (a b : A × B × S)
    (ha : allowedH (a.1 - b.1)) (hb : allowedG (a.2.1 - b.2.1))
    (hc : check (a.2.2 - b.2.2) =
      hCheck (a.1 - b.1) + gCheck (a.2.1 - b.2.1)) :
    AspisV8H1C2.SameUniformLaw
      (fun x => jointObservation hv gv hs gs x + a)
      (fun x => jointObservation hv gv hs gs x + b) := by
  obtain ⟨h, g, hh, hg, hshared⟩ := compatible_gluing hv gv hs gs
    allowedH allowedG check hCheck gCheck hCoverage hConsistency gCoverage
    (a.1 - b.1) (a.2.1 - b.2.1) (a.2.2 - b.2.2) ha hb hc
  apply affine_same_uniform_law (jointObservation hv gv hs gs) a b (h,g)
  change (hv h, gv g, hs h + gs g) = a - b
  rw [hh, hg, hshared]
  rfl
end Joint

#print axioms affine_translation_commutes
#print axioms affinePosteriorEquiv
#print axioms affine_fiber_counts
#print axioms affine_same_uniform_law
#print axioms jointObservation
#print axioms joint_affine_same_uniform_law
end AspisV8R17
