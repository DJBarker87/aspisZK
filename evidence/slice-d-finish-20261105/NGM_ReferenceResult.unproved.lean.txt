import NGM_FinishRef.Funs
import NGM_WordArrayEquality
set_option autoImplicit false
noncomputable section
namespace NGM_ReferenceResult
open Aeneas Aeneas.Std Result NGM_FinishRef
attribute [local instance] Classical.propDecidable
abbrev Word := Array U32 8#usize
abbrev R := core.result.Result Unit U8

def afterDot (next : Usize) (rhs : Word) : core.result.Result Word U8 → R
 | .Err error => .Err error
 | .Ok actual => if next=22#usize ∧ actual=rhs then .Ok () else .Err 5#u8

def afterPair (next : Usize) (rhs claim : Word) (dot : core.result.Result Word U8) :
 core.result.Result Word U8 → R
 | .Err error => .Err error
 | .Ok pair => if pair=claim then afterDot next rhs dot else .Err 3#u8

def afterClaim (next : Usize) (rhs : Word) (replies : Replies) : core.result.Result Word U8 → R
 | .Err error => .Err error
 | .Ok claim => match replies.weights with
   | .Err error => .Err error
   | .Ok () => afterPair next rhs claim replies.dot replies.pair

def result (two : Bool) (next : Usize) (rhs : Word) (replies : Replies) : R :=
 match replies.round0 with
 | .Err error => .Err error
 | .Ok first => afterClaim next rhs replies (if two then replies.round1 else .Ok first)

/-- Error codes 3 and 5 are the exact Relation and Query branches; every
other child error code is forwarded unchanged. No accepted-child premise. -/
theorem extraction_result (two : Bool) (next : Usize) (rhs : Word) (replies : Replies) :
 (do let observed ← finish_ref two next rhs replies;ok observed.result)=ok (result two next rhs replies) := by
 rcases replies with ⟨round0,round1,weights,pair,dot⟩
 cases two <;> cases round0 <;> cases round1 <;> cases weights <;> cases pair <;> cases dot <;>
  simp [finish_ref,event,Array.update,Array.repeat,NGM_WordArrayEquality.arrays_ne,
   result,afterClaim,afterPair,afterDot]
 all_goals split_ifs <;> simp_all
#print axioms extraction_result
end NGM_ReferenceResult
end
