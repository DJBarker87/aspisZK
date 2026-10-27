import XSd_DotFinish
import XRu_RowShape
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSd_DotFinishAll
/-- Entire finish transport for every exact source Dot; no count, canonicality
or independent success assumption. -/
theorem source (d : fast_pairing.canonical.Dot) :
 fast_pairing.canonical.Dot.finish d =
 AspisR1CanonicalDotFinish.canonical.Dot.finish (XRn_JoinedDot.cohort d) := by
 rcases d with ⟨sums⟩
 obtain ⟨a,b,c,d,rfl⟩ := XRu_RowShape.cells sums
 exact XSd_DotFinish.four_words a b c d
#print axioms source
end XSd_DotFinishAll
