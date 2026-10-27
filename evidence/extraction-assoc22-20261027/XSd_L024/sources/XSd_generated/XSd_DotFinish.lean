import XSd_DotReduce
import XRn_JoinedDot
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSd_DotFinish
/-- Entire selected finish on the SAME arbitrary four cells; results are
constructed from total reducers, not assumed successes. -/
theorem four_words (a b c d : U64) :
 fast_pairing.canonical.Dot.finish ⟨Array.make 4#usize [a,b,c,d]⟩=
 AspisR1CanonicalDotFinish.canonical.Dot.finish ⟨Array.make 4#usize [a,b,c,d]⟩ := by
 obtain ⟨w,hw,_,_⟩ := XSd_DotReduce.total a
 obtain ⟨x,hx,_,_⟩ := XSd_DotReduce.total b
 obtain ⟨y,hy,_,_⟩ := XSd_DotReduce.total c
 obtain ⟨z,hz,_,_⟩ := XSd_DotReduce.total d
 have hc0 := XRn_JoinedDot.reduce a
 have hc1 := XRn_JoinedDot.reduce b
 have hc2 := XRn_JoinedDot.reduce c
 have hc3 := XRn_JoinedDot.reduce d
 have map := XSd_DotSequence.four AspisR1CanonicalDotFinish.canonical.reduce a b c d w x y z
  (hc0.symm.trans hw) (hc1.symm.trans hx) (hc2.symm.trans hy) (hc3.symm.trans hz)
 unfold fast_pairing.canonical.Dot.finish AspisR1CanonicalDotFinish.canonical.Dot.finish
 rw [map,bind_tc_ok]
 have i0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize=ok a := rfl
 have i1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize=ok b := rfl
 have i2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize=ok c := rfl
 have i3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize=ok d := rfl
 simp only [i0,i1,i2,i3,hw,hx,hy,hz,bind_tc_ok]
#print axioms four_words
end XSd_DotFinish
