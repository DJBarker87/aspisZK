import NMT_345RSLCarriers
set_option autoImplicit false
namespace NMT_R2_WpResult
open Aeneas Aeneas.Std

theorem source {A : Type} (r : Result A) (post : A → Prop) (law : WP.spec r post) :
 ∃ value, r = .ok value ∧ post value := by
 cases hr : r with
 | fail e =>
  rw [hr] at law
  change False at law
  exact False.elim law
 | div =>
  rw [hr] at law
  change False at law
  exact False.elim law
 | ok value =>
  rw [hr] at law
  change post value at law
  exact ⟨value,rfl,law⟩
#print axioms source
end NMT_R2_WpResult
