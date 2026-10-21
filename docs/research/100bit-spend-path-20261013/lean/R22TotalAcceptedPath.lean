import R22TotalCheckedComposition

/-! Conditional cone totality suffices when the wrapping caller independently
establishes its domain on accepted runs. Checked acceptance is not assumed. -/
set_option autoImplicit false
namespace AspisR1.R22TotalAcceptedPath
open Aeneas Aeneas.Std Result R22TotalCheckedComposition

theorem accepted_path_R22 {ι α : Type} (code : ι → Code α)
    (domain : ι → Prop) (accepts : α → Prop)
    (caller_domain : ∀ x v, wrapping (code x) = ok v → accepts v → domain x)
    (total_on_domain : ∀ x, domain x → ∃ v, checked (code x) = ok v)
    (x : ι) (v : α) (hw : wrapping (code x) = ok v) (ha : accepts v) :
    NoOverflow (code x) ∧ checked (code x) = ok v := by
  have hd := caller_domain x v hw ha
  obtain ⟨hs, he⟩ := reached_refinement_R22 code domain total_on_domain x hd
  exact ⟨hs, he.symm.trans hw⟩

#print axioms accepted_path_R22
end AspisR1.R22TotalAcceptedPath
