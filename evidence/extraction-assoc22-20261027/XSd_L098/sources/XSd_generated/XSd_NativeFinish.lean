import XSd_DotFinishAll
import LPf_DotFinish
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSd_NativeFinish
/-- Exact native/cohort finish endpoint on SAME arbitrary raw accumulator words.
No successful output, count or canonical operand premise. -/
theorem source (d : fast_pairing.canonical.Dot) :
 fast_pairing.canonical.Dot.finish d =
 FIo_Native.fast_pairing.canonical.Dot.finish ⟨d.sums⟩ := by
 unfold fast_pairing.canonical.Dot.finish FIo_Native.fast_pairing.canonical.Dot.finish
 simp only [XSd_DotReduce.body]
 rfl

/-- Universal success witness for the actual kit finish; arbitrary initial
U64 cells are covered, including values outside ordinary no-wrap histories. -/
theorem total (d : fast_pairing.canonical.Dot) :
 ∃ out, fast_pairing.canonical.Dot.finish d=ok out := by
 rcases d with ⟨sums⟩
 obtain ⟨a,b,c,d,rfl⟩ := XRu_RowShape.cells sums
 obtain ⟨w,x,y,z,run,_,_,_,_,_,_,_,_⟩ := AspisR1.LPf_DotFinish.source a b c d
 exact ⟨Array.make 4#usize [w,x,y,z],(source _).trans run⟩
#print axioms source
#print axioms total
end XSd_NativeFinish
