import NGM_ReferenceTotal
set_option autoImplicit false
noncomputable section
namespace NGM_ReferenceResult
open Aeneas Aeneas.Std Result NGM_FinishRef
attribute [local instance] Classical.propDecidable
/-- The complete two-fold extracted Result accepts only after every child
returns its successful reply and both exact comparisons hold. -/
theorem accepted_iff (next : Usize) (rhs : Word) (replies : Replies) :
 project true next rhs replies=ok (.Ok ()) ↔
 ∃ first claim, replies.round0=.Ok first ∧ replies.round1=.Ok claim ∧
 replies.weights=.Ok () ∧ replies.pair=.Ok claim ∧ replies.dot=.Ok rhs ∧ next=22#usize := by
 rw [extraction_result_s2]
 rcases replies with ⟨r0,r1,w,p,d⟩
 cases r0 <;> cases r1 <;> cases w <;> cases p <;> cases d <;>
 simp [result,afterClaim,afterPair,afterDot] <;> aesop
#print axioms accepted_iff
end NGM_ReferenceResult
end
