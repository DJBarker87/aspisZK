import XRn_Join_Funs
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_QueryRead
/-- Reached read gives the bound in the SAME source query. -/
theorem bound (p : verifier.Prepared) (a : verifier.Accumulator) (word : U32)
 (h : Array.index_usize p.queries a.next=ok word) : a.next.val<22 := by
 by_contra bad
 have len : p.queries.val.length=22 := p.queries.property
 have absent : p.queries.val[a.next.val]?=none := List.getElem?_eq_none (by omega)
 simp [Array.index_usize,absent] at h
#print axioms bound
end XRr_QueryRead
