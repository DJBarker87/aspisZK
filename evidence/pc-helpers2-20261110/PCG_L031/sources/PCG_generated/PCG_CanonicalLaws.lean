import PCG_HelperRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_CanonicalLaws

theorem step (prefix : Bool) (word : U32) :
 PCG_HelperRef.canonical_step prefix word =
 ok (prefix && decide (word.val < 2147483647)) := by
 cases prefix
 · simp [PCG_HelperRef.canonical_step]
 · by_cases h : word < 2147483647#u32
   · have hv : word.val < 2147483647 := by scalar_tac
     simp [PCG_HelperRef.canonical_step,h,hv]
   · have hv : ¬ word.val < 2147483647 := by scalar_tac
     simp [PCG_HelperRef.canonical_step,h,hv]

def run (prefix : Bool) : List U32 → Result Bool
 | [] => ok prefix
 | word::words => do
   let next ← PCG_HelperRef.canonical_step prefix word
   run next words

/-- Arbitrary pre-state and decreasing suffix; no concrete digest loop reduction. -/
theorem suffix (words : List U32) (prefix : Bool) :
 run prefix words = ok (prefix && words.all (fun w => decide (w.val < 2147483647))) := by
 induction words generalizing prefix with
 | nil => simp [run]
 | cons w ws ih => simp only [run,step,bind_tc_ok,ih,List.all_cons,Bool.and_assoc]

def digest (words : Array U32 8#usize) : Result Bool := run true words.val

theorem row_186 (words : Array U32 8#usize) :
 digest words = ok (decide (∀ w ∈ words.val, w.val < 2147483647)) := by
 rw [digest,suffix]
 simp

#print axioms step
#print axioms suffix
#print axioms row_186
end PCG_CanonicalLaws
