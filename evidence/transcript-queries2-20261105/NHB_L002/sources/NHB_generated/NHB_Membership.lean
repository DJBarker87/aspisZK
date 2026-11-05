import NGQ_COMBINED_IMPORT
set_option autoImplicit false
namespace AspisR1.NHB_Membership
open Aeneas Aeneas.Std Result
/-- Reviewed transcription of the scalar disjunction in NHB_contains_ref.
The array reference reads the first n elements; this list is that SAME prefix. -/
def reference (x : U32) : List U32 → Bool
  | [] => false
  | y::ys => if y=x then true else reference x ys

theorem reference_eq (x : U32) (xs : List U32) :
    reference x xs = decide (x ∈ xs) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : y=x
    · subst y
      simp only [reference,↓reduceIte,List.mem_cons_self,decide_true]
    · simp only [reference,h,↓reduceIte,ih,List.mem_cons]
      simp only [eq_comm, h, false_or]

/-- Membership equality in the exact carrier consumed by NGQ's word-step law. -/
theorem prefix (x : U32) (s : NGQ_SamplerTrace.State) :
    reference x (s.accepted.val.take s.accepted_len.val) =
      decide (x.val ∈ Query31ExplicitScanBody.acceptedPrefix s) := by
  rw [reference_eq]
  exact congrArg decide (propext (NGQ_SamplerStep.val_mem _ x).symm)

#print axioms reference_eq
#print axioms prefix
end AspisR1.NHB_Membership
