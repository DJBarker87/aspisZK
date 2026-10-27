import XRn_JoinedDot
open Aeneas Aeneas.Std Result
open XRn_Join_Release
set_option autoImplicit false
namespace XRn_JoinedDotFinish
/-- Four symbolic accumulator cells, never a concrete large recurrence. -/
theorem four_words (a b c d : U64) :
 fast_pairing.canonical.Dot.finish ⟨Array.make 4#usize [a,b,c,d]⟩=
 AspisR1CanonicalDotFinish.canonical.Dot.finish ⟨Array.make 4#usize [a,b,c,d]⟩ := by
 unfold fast_pairing.canonical.Dot.finish AspisR1CanonicalDotFinish.canonical.Dot.finish
 simp only [XRn_JoinedDot.reduce]
 rfl
#print axioms four_words
end XRn_JoinedDotFinish
