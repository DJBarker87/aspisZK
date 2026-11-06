import NGT_NBL_DecodeNative
set_option autoImplicit false
namespace AspisR1.NKD_Decode
open Aeneas Aeneas.Std Result ExtractedIndexedAddSmallNatModelV1
/-- TX1:157: exact eight returned coordinates; domain is established by low/add. -/
theorem root (digits : Digits) (canonical : Canonical digits) :
 AspisR1Post25Sampler.sampler.decode8 digits = ok (NGT_NBL_DecodeNative.pack digits) :=
 NGT_NBL_DecodeNative.source digits canonical
#print root
#print axioms root
end AspisR1.NKD_Decode
