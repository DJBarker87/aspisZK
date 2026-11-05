import NHP_StackRef.Funs
import NHC_ErrorConversion
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHP_StackLaw

theorem result (height : Usize) :
    NHP_StackRef.NHP_reference.transaction_level height = ok (decide (height.val = 1)) := by
  have heq : height = 1#usize ↔ height.val = 1 := by
    constructor
    · intro h; subst height; rfl
    · intro h; exact UScalar.eq_of_val_eq h
  change ok (decide (height = 1#usize)) = ok (decide (height.val = 1))
  simp only [heq]
#print axioms result

theorem admitted (height : Usize) :
    NHP_StackRef.NHP_reference.transaction_level height = ok true ↔ height.val = 1 := by
  rw [result]
  simp
#print axioms admitted

theorem forbidden_error :
    NGK_NFR_CHelper.convertPoolError .CpiInvocationForbidden =
      ok (AdapterRw.solana_program_error.ProgramError.Custom 0x41532036#u32) := by
  exact NHC_ErrorConversion.result .CpiInvocationForbidden
#print axioms forbidden_error

def reply (height : Usize) : Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError) := do
  let allowed ← NHP_StackRef.NHP_reference.transaction_level height
  if allowed then ok (.Ok ()) else do
    let error ← NGK_NFR_CHelper.convertPoolError .CpiInvocationForbidden
    ok (.Err error)

theorem exact_reply (height : Usize) :
    reply height = ok (if height.val = 1 then .Ok ()
      else .Err (AdapterRw.solana_program_error.ProgramError.Custom 0x41532036#u32)) := by
  simp only [reply,result,bind_tc_ok]
  by_cases h : height.val = 1 <;> simp [h,forbidden_error]
#print axioms exact_reply
end NHP_StackLaw
