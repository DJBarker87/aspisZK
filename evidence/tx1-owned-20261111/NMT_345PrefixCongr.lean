import NMT_345PrefixFold
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Only congruence of the eight established call boundaries. -/
theorem prefix_congr {W : Type} (c : Calls) (s : Selected W)
 (f g : Decoded W → Result Ret) (same : ∀ d,f d = g d) :
 prefixFold c s f = prefixFold c s g := by
 unfold prefixFold
 apply try_congr
 intro _
 apply try_congr
 intro _
 apply try_congr
 intro _
 apply try_congr
 intro _
 apply try_congr
 intro ck
 apply try_congr
 intro _
 apply try_congr
 intro pub
 apply try_congr
 intro statement
 exact same _
#print axioms prefix_congr
end NMT_345
