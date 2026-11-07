import NMP_ResultTransport
import NGX_PrefixCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_Install138
open Aeneas Aeneas.Std Result NMP_ResultTransport NMP_Transport
/-- Existing CLOSED parser source, adapted only through checked type inverses. -/
def parse (bytes : Slice U8) := outer (inner fromT13 fromT12)
 (NGX_PrefixCarrier.result (AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes))
/-- At the SAME bytes, conversion back is exactly the CLOSED parser packet's
full Result. No borrowed-prefix origin or success premise is added. -/
theorem same (bytes : Slice U8) :
 outer (inner toT13 toT12) (parse bytes) =
 NGX_PrefixCarrier.result (AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes) := by
 apply outer_inverse
 intro r
 exact inner_inverse fromT13 toT13 fromT12 toT12 fromT13_inverse fromT12_inverse r
#print axioms same
end AspisR1.NMP_Install138
