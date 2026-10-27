import R1Z.PV_CB_Op105Exact
import R1Z.PV_CB_Op107Exact
import R1Z.PV_CB_Op109Exact
import R1Z.PV_CB_Op118Exact

-- Focused audit of newly discharged source laws and their generic/carrier helpers.
-- The all-row candidate audit remains separately blocked on the recorded cache closure.
#print axioms R1Z.PV_CB_Op105Exact.op105_source
#print axioms R1Z.PV_CB_Op107Transport.native_roundtrip
#print axioms R1Z.PV_CB_Op107Transport.extracted_roundtrip
#print axioms R1Z.PV_CB_OptionDiscriminant.none_tag
#print axioms R1Z.PV_CB_OptionDiscriminant.some_tag
#print axioms R1Z.PV_CB_Op107Exact.op107_source
#print axioms R1Z.PV_CB_ArrayTransport.roundtrip
#print axioms R1Z.PV_CB_Op109RefTransport.native_roundtrip
#print axioms R1Z.PV_CB_Op109RefTransport.extracted_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.native_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.extracted_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.native_wide_roundtrip
#print axioms R1Z.PV_CB_Op109Transport.extracted_wide_roundtrip
#print axioms R1Z.PV_CB_Op109CanonicalBinding.reference_equation
#print axioms R1Z.PV_CB_Op109Exact.op109_source
#print axioms R1Z.PV_CB_Op118Transport.native_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.extracted_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.native_array_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.extracted_array_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.native_points_roundtrip
#print axioms R1Z.PV_CB_Op118Transport.extracted_points_roundtrip
#print axioms R1Z.PV_CB_Op118Exact.op118_source
