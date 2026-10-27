import LPf_PublicDotFinish
import LPf_ArrayFour
set_option autoImplicit false
namespace AspisR1.LPf_PublicDotAllStates
open Aeneas Aeneas.Std Result

/-- Every native accumulator carrier is included, not just a chosen history or
an empty/fixed state. This theorem still says nothing about Q.raw or push. -/
theorem source (state : FIo_Native.fast_pairing.EbyKDot) : ∃ out,
    FIo_Native.fast_pairing.EbyKDot.finish state = ok out ∧
    out.c0.c0.a.val = (state.c0.sums.val[0]!).val % 2147483647 ∧
    out.c0.c0.b.val = (state.c0.sums.val[1]!).val % 2147483647 ∧
    out.c0.c1.a.val = (state.c0.sums.val[2]!).val % 2147483647 ∧
    out.c0.c1.b.val = (state.c0.sums.val[3]!).val % 2147483647 ∧
    out.c1.c0.a.val = (state.c1.sums.val[0]!).val % 2147483647 ∧
    out.c1.c0.b.val = (state.c1.sums.val[1]!).val % 2147483647 ∧
    out.c1.c1.a.val = (state.c1.sums.val[2]!).val % 2147483647 ∧
    out.c1.c1.b.val = (state.c1.sums.val[3]!).val % 2147483647 := by
  rcases state with ⟨⟨left⟩,⟨right⟩,count⟩
  obtain ⟨a,b,c,d,hl⟩ := LPf_ArrayFour.shape left
  obtain ⟨e,f,g,h,hr⟩ := LPf_ArrayFour.shape right
  subst left
  subst right
  simpa [Array.make] using LPf_PublicDotFinish.source a b c d e f g h count

#print axioms source
end AspisR1.LPf_PublicDotAllStates
