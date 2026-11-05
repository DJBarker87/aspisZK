import NGM_ReferenceTail
set_option autoImplicit false
noncomputable section
namespace NGM_ReferenceResult
open Aeneas Aeneas.Std Result NGM_FinishRef
attribute [local instance] Classical.propDecidable
/-- Complete deployed two-fold Result. The earlier prefix lemmas are used
instead of re-expanding every event update in all reply combinations. -/
theorem extraction_result_s2 (next : Usize) (rhs : Word) (replies : Replies) :
 project true next rhs replies=ok (result true next rhs replies) := by
 rcases replies with ⟨r0,r1,weights,pair,dot⟩
 cases r0 with
 | Err error => simpa [result] using first_error true next rhs error r1 pair dot weights
 | Ok first =>
  cases r1 with
  | Err error => simpa [result,afterClaim] using second_error next rhs first error weights pair dot
  | Ok claim =>
   cases weights with
   | Err error => simpa [result,afterClaim] using weights_error next rhs first claim error pair dot
   | Ok unit =>
    cases unit
    cases pair with
    | Err error => simpa [result,afterClaim,afterPair] using pair_error next rhs first claim error dot
    | Ok value =>
     by_cases equal : value=claim
     · subst value
       cases dot with
       | Err error => simpa [result,afterClaim,afterPair,afterDot] using dot_error next rhs first claim error
       | Ok actual =>
        by_cases counter : next=22#usize
        · subst next
          by_cases final : actual=rhs
          · subst actual
            simpa [result,afterClaim,afterPair,afterDot] using accepted rhs first claim
          · simpa [result,afterClaim,afterPair,afterDot,final] using value_mismatch rhs first claim actual final
        · simpa [result,afterClaim,afterPair,afterDot,counter] using counter_mismatch next rhs first claim actual counter
     · simpa [result,afterClaim,afterPair,equal] using pair_mismatch next rhs first claim value dot equal
#print axioms extraction_result_s2
end NGM_ReferenceResult
end
