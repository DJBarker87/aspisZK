import NKD_Low
import NKD_Decode
import NGT_NBL_SamplerNative
set_option autoImplicit false
namespace AspisR1.NKD_Ordinary
open Aeneas Aeneas.Std Result NGT_NBL_SamplerReplay
/-- TX1:160: low-child result and decoder canonicality are discharged on the SAME trace. -/
theorem root (block : Bytes32) (digits q : Words) (cut : NKD_Low.Cut block digits q) :
 NGT_NBA_Installed.actual.sampling.ordinary block =
 ok (AspisR1Post25SamplerPreparedCarrier.candidateToPE (NGT_NBL_DecodeNative.pack digits)) :=
 NGT_NBL_SamplerNative.ordinary block digits q cut
#print root
#print axioms root
end AspisR1.NKD_Ordinary
