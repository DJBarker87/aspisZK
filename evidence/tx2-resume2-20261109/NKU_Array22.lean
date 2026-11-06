import NKU_Validator
set_option autoImplicit false
namespace NKU_Array22
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
theorem source (qs : Array U32 22#usize) : NKU_Validator.values qs.val=ok qs := by
 rcases qs with ⟨xs,size⟩
 rcases xs with _ | ⟨q0,xs⟩
 · simp at size
 rcases xs with _ | ⟨q1,xs⟩
 · simp at size
 rcases xs with _ | ⟨q2,xs⟩
 · simp at size
 rcases xs with _ | ⟨q3,xs⟩
 · simp at size
 rcases xs with _ | ⟨q4,xs⟩
 · simp at size
 rcases xs with _ | ⟨q5,xs⟩
 · simp at size
 rcases xs with _ | ⟨q6,xs⟩
 · simp at size
 rcases xs with _ | ⟨q7,xs⟩
 · simp at size
 rcases xs with _ | ⟨q8,xs⟩
 · simp at size
 rcases xs with _ | ⟨q9,xs⟩
 · simp at size
 rcases xs with _ | ⟨q10,xs⟩
 · simp at size
 rcases xs with _ | ⟨q11,xs⟩
 · simp at size
 rcases xs with _ | ⟨q12,xs⟩
 · simp at size
 rcases xs with _ | ⟨q13,xs⟩
 · simp at size
 rcases xs with _ | ⟨q14,xs⟩
 · simp at size
 rcases xs with _ | ⟨q15,xs⟩
 · simp at size
 rcases xs with _ | ⟨q16,xs⟩
 · simp at size
 rcases xs with _ | ⟨q17,xs⟩
 · simp at size
 rcases xs with _ | ⟨q18,xs⟩
 · simp at size
 rcases xs with _ | ⟨q19,xs⟩
 · simp at size
 rcases xs with _ | ⟨q20,xs⟩
 · simp at size
 rcases xs with _ | ⟨q21,xs⟩
 · simp at size
 cases xs with
 | nil => rfl
 | cons q rest => simp at size
#print axioms source
end NKU_Array22
