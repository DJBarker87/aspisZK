import NMS_R2N_AllocationRegular
set_option autoImplicit false
namespace NMS_R2N_RegularControl
open Aeneas Aeneas.Std
/-- Symbolic conditional composition: no concrete buffer or Bool reduction. -/
theorem branch {A : Type} (p : Prop) [Decidable p]
 (yes no : RSL.Spec A) (yesCode noCode : Result A)
 (onYes : NMS_R2N_Regular.Law yes yesCode) (onNo : NMS_R2N_Regular.Law no noCode) :
 NMS_R2N_Regular.Law (if p then yes else no) (if p then yesCode else noCode) := by
 by_cases selected : p
 · simpa only [if_pos selected] using onYes
 · simpa only [if_neg selected] using onNo
#print axioms branch
end NMS_R2N_RegularControl
