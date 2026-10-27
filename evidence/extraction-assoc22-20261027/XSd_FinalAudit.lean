import XSd_A1Audit
import XSd_NativeFinish
import XSd_InverseCompare
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSd_FinalValue
/-- Every selected finish succeeds, and all four SAME cells have the exact
canonical field residues. No history/no-wrap/canonicality premise is needed. -/
theorem source (d : fast_pairing.canonical.Dot) :
 ∃ out : fast_pairing.canonical.Q,
 fast_pairing.canonical.Dot.finish d=ok out ∧
 ∀ i : Fin 4, (out.val[i.val]'(by have h : out.val.length=4 := out.property; omega)).val =
  (d.sums.val[i.val]'(by have h : d.sums.val.length=4 := d.sums.property; omega)).val%2147483647 := by
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
end XSd_FinalValue

#print axioms XSd_InverseShape.even
#print axioms XSd_InverseShape.one_mul
#print axioms XSd_InverseShape.spine_one
#print axioms XSd_InverseShape.inverse_spine
#print axioms XSd_InverseCompare.kit_two
#print axioms XSd_InverseCompare.cohort_two
#print axioms XSd_InverseCompare.mismatch
#print axioms XSd_InverseCompare.both_success
#print axioms XSd_DotSequence.sequence
#print axioms XSd_DotSequence.four
#print axioms XSd_MapState.source
#print axioms XSd_ArrayMap.source
#print axioms XSd_DotReduce.body
#print axioms XSd_DotReduce.total
#print axioms XSd_DotFinish.four_words
#print axioms XSd_DotFinishAll.source
#print axioms XSd_NativeFinish.source
#print axioms XSd_NativeFinish.total
#print axioms LPk_Result.native_result
#print axioms XRz_HybridSampler.ordinary
#print axioms XRz_HybridSampler.gamma
