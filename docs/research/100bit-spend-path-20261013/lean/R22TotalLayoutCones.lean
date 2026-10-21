import R22TotalCheckedComposition
import PreparedFromQmSourceBridge
import FourDotsWideLimbCanonicalV1

set_option autoImplicit false
namespace AspisR1.R22TotalLayoutCones
open Aeneas Aeneas.Std Result R22TotalCheckedComposition

theorem qm_embedding_R22
    (t : Translation AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmSource) :
    ∀ x, NoOverflow (t.code x) ∧ wrapping (t.code x) =
      AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmSource x := by
  apply extracted_total_R22
  intro x
  exact ⟨_, AspisR1PublicPreparation.PreparedFromQmSourceBridge.fromQmSource_success x⟩

theorem eight_limb_layout_R22 (t : Translation AspisR1EbyKPushWideToQ.toLimbs) :
    ∀ x, NoOverflow (t.code x) ∧ wrapping (t.code x) = AspisR1EbyKPushWideToQ.toLimbs x := by
  apply extracted_total_R22
  intro x
  exact ⟨_, AspisR1FastDotsWideLimbCanonical.toLimbs_actual_value x⟩

#print axioms qm_embedding_R22
#print axioms eight_limb_layout_R22
end AspisR1.R22TotalLayoutCones
