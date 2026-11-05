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

def project (two : Bool) (next : Usize) (rhs : Word) (replies : Replies) : Result R := do
 let observed ← finish_ref two next rhs replies
 ok observed.result

@[simp] theorem small_mod (n : Nat) (small : n<8) : n%Usize.size=n := by
 have room : 8<Usize.size := by scalar_tac
 exact Nat.mod_eq_of_lt (by omega)
#print axioms small_mod

theorem first_error (two : Bool) (next : Usize) (rhs : Word) (error : U8)
 (round1 pair dot : core.result.Result Word U8) (weights : core.result.Result Unit U8) :
 project two next rhs ⟨.Err error,round1,weights,pair,dot⟩=ok (.Err error) := by
 simp [project,finish_ref,event,Array.update,Array.repeat,lift,Usize.wrapping_add]

theorem second_error (next : Usize) (rhs first : Word) (error : U8) (weights : core.result.Result Unit U8) (pair dot : core.result.Result Word U8) :
 project true next rhs ⟨.Ok first,.Err error,weights,pair,dot⟩=ok (.Err error) := by
 simp [project,finish_ref,event,Array.update,Array.repeat,lift,Usize.wrapping_add,NGM_WordArrayEquality.arrays_ne]

theorem weights_error (next : Usize) (rhs first : Word) (claim : Word) (error : U8) (pair dot : core.result.Result Word U8) :
 project true next rhs ⟨.Ok first,.Ok claim,.Err error,pair,dot⟩=ok (.Err error) := by
 simp [project,finish_ref,event,Array.update,Array.repeat,lift,Usize.wrapping_add,NGM_WordArrayEquality.arrays_ne]

theorem pair_error (next : Usize) (rhs first : Word) (claim : Word) (error : U8) (dot : core.result.Result Word U8) :
 project true next rhs ⟨.Ok first,.Ok claim,.Ok (),.Err error,dot⟩=ok (.Err error) := by
 simp [project,finish_ref,event,Array.update,Array.repeat,lift,Usize.wrapping_add,NGM_WordArrayEquality.arrays_ne]

theorem pair_mismatch (next : Usize) (rhs first : Word) (claim pair : Word) (dot : core.result.Result Word U8) (different : pair≠claim) :
 project true next rhs ⟨.Ok first,.Ok claim,.Ok (),.Ok pair,dot⟩=ok (.Err 3#u8) := by
 simp [project,finish_ref,event,Array.update,Array.repeat,lift,Usize.wrapping_add,NGM_WordArrayEquality.arrays_ne,different]

#print axioms first_error
#print axioms second_error
#print axioms weights_error
#print axioms pair_error
#print axioms pair_mismatch
end NGM_ReferenceResult
end
