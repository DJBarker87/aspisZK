import XSd_NativeFinish
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSd_DotFinishValue
/-- Every selected finish succeeds, and all four SAME cells have the exact
canonical field residues. No history/no-wrap/canonicality premise is needed. -/
theorem source (d : fast_pairing.canonical.Dot) :
 ∃ out : fast_pairing.canonical.Q,
 fast_pairing.canonical.Dot.finish d=ok out ∧
 ∀ i : Fin 4, (out.val[i.val]'(by have h := out.property; omega)).val =
  (d.sums.val[i.val]'(by have h := d.sums.property; omega)).val%2147483647 := by
 rcases d with ⟨sums⟩
 obtain ⟨a,b,c,d,rfl⟩ := XRu_RowShape.cells sums
 obtain ⟨w,x,y,z,run,v0,v1,v2,v3,_,_,_,_⟩ := AspisR1.LPf_DotFinish.source a b c d
 refine ⟨Array.make 4#usize [w,x,y,z],(XSd_NativeFinish.source _).trans run,?_⟩
 rintro ⟨i,hi⟩
 have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
 rcases cases with rfl | rfl | rfl | rfl
 · exact v0
 · exact v1
 · exact v2
 · exact v3
#print axioms source
end XSd_DotFinishValue
