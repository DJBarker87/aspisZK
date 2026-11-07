import PCG_HelperRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_CanonicalLaws

theorem step (seen : Bool) (word : U32) :
 PCG_HelperRef.canonical_step seen word =
 ok (seen && decide (word.val < 2147483647)) := by
 cases seen
 · simp [PCG_HelperRef.canonical_step]
 · by_cases h : word < 2147483647#u32
   · have hv : word.val < 2147483647 := by scalar_tac
     simp [PCG_HelperRef.canonical_step,h,hv]
   · have hv : ¬ word.val < 2147483647 := by scalar_tac
     simp [PCG_HelperRef.canonical_step,h,hv]

def run (seen : Bool) : List U32 → Result Bool
 | [] => ok seen
 | word::words => do
   let next ← PCG_HelperRef.canonical_step seen word
   run next words

/-- Arbitrary pre-state and decreasing suffix; no concrete digest loop reduction. -/
theorem suffix (words : List U32) (seen : Bool) :
 run seen words = ok (seen && words.all (fun w => decide (w.val < 2147483647))) := by
 induction words generalizing seen with
 | nil => simp [run]
 | cons w ws ih => simp only [run,step,bind_tc_ok,ih,List.all_cons,Bool.and_assoc]

def digest (words : Array U32 8#usize) : Result Bool := run true words.val

theorem row_186 (words : Array U32 8#usize) :
 digest words = ok (decide (∀ w ∈ words.val, w.val < 2147483647)) := by
 rw [digest,suffix]
 simp only [Bool.true_and]
 apply congrArg Result.ok
 have hall : words.val.all (fun w => decide (w.val < 2147483647)) = true ↔
   ∀ w ∈ words.val, w.val < 2147483647 := by simp
 cases h : words.val.all (fun w => decide (w.val < 2147483647))
 · have hp : ¬ ∀ w ∈ words.val, w.val < 2147483647 := by
     intro hp
     have ht := hall.mpr hp
     rw [h] at ht
     contradiction
   simp [hp]
 · have hp := hall.mp h
   simp [hp]

#print axioms step
#print axioms suffix
#print axioms row_186
end PCG_CanonicalLaws
