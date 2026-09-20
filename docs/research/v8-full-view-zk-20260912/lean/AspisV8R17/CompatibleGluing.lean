import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Tactic.Abel

/-! Compatible-image composition, with all coverage/compatibility premises
explicit. No source rank, uniform posterior, or hiding assumption is proved
or introduced by this conditional algebraic lemma. -/
set_option autoImplicit false
namespace AspisV8R17
variable {H G A B S E : Type*} [AddCommGroup S] [AddCommGroup E]

/-- First choose an H preimage of its retained observations; then use G's
compatible image to cancel H's contribution to the shared messages.
`E` can contain several equations, e.g. semantic terminal and relation
evaluation simultaneously. Dropping an equation is not authorized here. -/
theorem compatible_gluing
    (hv : H → A) (gv : G → B) (hs : H → S) (gs : G → S)
    (allowedH : A → Prop) (allowedG : B → Prop)
    (check : S →+ E) (hCheck : A → E) (gCheck : B → E)
    (hCoverage : ∀ a, allowedH a → ∃ h, hv h = a)
    (hConsistency : ∀ h, check (hs h) = hCheck (hv h))
    (gCoverage : ∀ b s, allowedG b → check s = gCheck b →
      ∃ g, gv g = b ∧ gs g = s)
    (a : A) (b : B) (s : S) (ha : allowedH a) (hb : allowedG b)
    (compatible : check s = hCheck a + gCheck b) :
    ∃ h g, hv h = a ∧ gv g = b ∧ hs h + gs g = s := by
  obtain ⟨h, hh⟩ := hCoverage a ha
  have hc : check (s - hs h) = gCheck b := by
    rw [map_sub, compatible, hConsistency, hh]
    abel
  obtain ⟨g, hg, hgs⟩ := gCoverage b (s - hs h) hb hc
  refine ⟨h, g, hh, hg, ?_⟩
  rw [hgs]
  abel

/-- The reverse inclusion needs both channels' actual consistency laws.
It does not follow just from lower-rank certificates. -/
theorem joint_image_compatible
    (hv : H → A) (gv : G → B) (hs : H → S) (gs : G → S)
    (check : S →+ E) (hCheck : A → E) (gCheck : B → E)
    (hConsistency : ∀ h, check (hs h) = hCheck (hv h))
    (gConsistency : ∀ g, check (gs g) = gCheck (gv g))
    (h : H) (g : G) :
    check (hs h + gs g) = hCheck (hv h) + gCheck (gv g) := by
  rw [map_add, hConsistency, gConsistency]

#print axioms compatible_gluing
#print axioms joint_image_compatible
end AspisV8R17
