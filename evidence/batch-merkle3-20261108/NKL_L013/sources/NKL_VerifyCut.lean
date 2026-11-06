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
   exact cut.indices ⟨j,by simpa only [afterIdx.property,show (16#usize).val=16 from rfl] using left⟩

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
     exact cut.values ⟨j,by simpa only [afterVal.property,show (16#usize).val=16 from rfl] using left⟩
       ⟨k,by simpa only [(afterVal.val[j]).property,show (32#usize).val=32 from rfl] using a⟩

set_option pp.proofs false
#print result
#print axioms result
#print axioms indices
#print axioms values
end NKL_VerifyCut
