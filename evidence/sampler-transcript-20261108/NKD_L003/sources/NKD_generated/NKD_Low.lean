import NGT_NBL_SamplerReplay
set_option autoImplicit false
namespace AspisR1.NKD_Low
open Aeneas Aeneas.Std Result ExtractedIndexedAddSmallNatModelV1 NGT_NBL_SamplerReplay
/-- The reviewed cut is the source-ordered eight-pass trace, not an endpoint equation. -/
abbrev Cut := LowTrace
/-- TX1:159: complete pair and the domains consumed at both sample callers. -/
theorem root (block : Bytes32) (digits q : Words) (cut : Cut block digits q) :
 AspisR1Post25Sampler.sampler.low_base_p_digits block = ok (digits,quotient q) ∧
 Canonical digits ∧ (quotient q).val ≤ 256 := low block digits q cut
#print root
#print axioms root
end AspisR1.NKD_Low
