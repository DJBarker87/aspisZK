import NKL_ExitTransport
set_option autoImplicit false
namespace NKL_VerifyCut
open Aeneas Aeneas.Std Result
open NKL_ExitTransport

def isOk : Reply → Bool | .Ok _ => true | .Err _ => false

/-- K005/K006 assertions, after the child log receives its arbitrary full
post-state. The child writes BOTH complete arrays; no pre-state frame is
asserted. Call arguments and byte windows are documented in NKL_SEGMENTS.md. -/
structure Cut (valid : Bool) (postIdx : Indices) (postVal : Values)
 (out : Reply) (afterIdx : Indices) (afterVal : Values) : Prop where
 tag : isOk out = valid
 error : valid=false → out=.Err .Merkle
 indices : ∀ j : Fin 16, afterIdx.val[j.val]! = postIdx.val[j.val]!
 values : ∀ (j : Fin 16) (k : Fin 32),
  (afterVal.val[j.val]!).val[k.val]! = (postVal.val[j.val]!).val[k.val]!

theorem result (valid : Bool) (postIdx : Indices) (postVal : Values)
 (out : Reply) (afterIdx : Indices) (afterVal : Values)
 (cut : Cut valid postIdx postVal out afterIdx afterVal) :
 out = if valid then .Ok () else .Err .Merkle := by
 cases valid with
 | false => exact cut.error rfl
 | true => cases out with
   | Ok u => cases u; rfl
   | Err e => have impossible:=cut.tag; cases impossible

/-- Extensional recovery of the full output arrays from the universally
quantified arbitrary-cell assertions. No successful-child premise. -/
theorem indices (valid : Bool) (postIdx : Indices) (postVal : Values)
 (out : Reply) (afterIdx : Indices) (afterVal : Values)
 (cut : Cut valid postIdx postVal out afterIdx afterVal) : afterIdx=postIdx := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact afterIdx.property.trans postIdx.property.symm
 · intro j left right
   have length : afterIdx.val.length=16 := afterIdx.property
   simpa only [getElem!_pos _ _ left,getElem!_pos _ _ right] using cut.indices ⟨j,by omega⟩

theorem values (valid : Bool) (postIdx : Indices) (postVal : Values)
 (out : Reply) (afterIdx : Indices) (afterVal : Values)
 (cut : Cut valid postIdx postVal out afterIdx afterVal) : afterVal=postVal := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact afterVal.property.trans postVal.property.symm
 · intro j left right
   apply Subtype.ext
   apply List.ext_getElem
   · exact (afterVal.val[j]).property.trans (postVal.val[j]).property.symm
   · intro k a b
     have outer : afterVal.val.length=16 := afterVal.property
     have inner : (afterVal.val[j]).val.length=32 := (afterVal.val[j]).property
     simpa only [getElem!_pos _ _ left,getElem!_pos _ _ right,
       getElem!_pos _ _ a,getElem!_pos _ _ b] using cut.values ⟨j,by omega⟩ ⟨k,by omega⟩

set_option pp.proofs false
#print result
#print axioms result
#print axioms indices
#print axioms values
end NKL_VerifyCut
