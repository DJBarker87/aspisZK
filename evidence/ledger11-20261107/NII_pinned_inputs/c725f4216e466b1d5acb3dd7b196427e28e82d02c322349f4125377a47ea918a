import NGL_ErrorModel
set_option autoImplicit false
namespace NHD_ErrorLabels
open NGL_ErrorModel

def casesTable : List (E × String) :=
  [(.Parse,"r1:error:Parse"),(.Semantic,"r1:error:Semantic"),
   (.Transcript,"r1:error:Transcript"),(.Relation,"r1:error:Relation"),
   (.Merkle,"r1:error:Merkle"),(.Query,"r1:error:Query"),
   (.Checkpoint,"r1:error:Checkpoint"),(.Allocation,"r1:error:Allocation")]

/-- The finite cases are exact, including the enum input associated with each log. -/
theorem exhaustive (e : E) : (e,message e) ∈ casesTable := by
  cases e <;> simp [casesTable,message,label]

/-- Every rendering fits the native local writer. Only these tiny strings reduce. -/
theorem writer_bound (e : E) : (message e).utf8ByteSize ≤ 24 := by
  cases e <;> decide

/-- The dispatcher cannot silently identify two different error labels. -/
theorem distinct (e f : E) (same : message e = message f) : e = f := by
  cases e <;> cases f <;> simp_all [message,label]

#print axioms exhaustive
#print axioms writer_bound
#print axioms distinct
end NHD_ErrorLabels
