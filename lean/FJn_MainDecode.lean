import FIr_CarrierCanonical
import FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MainDecode
/-- Coordinate-only main/native adapter preserves the exact decoded value. -/
theorem value (q : FIq_Carriers.MQ) : FIv_NativeValue.decode (FIq_Carriers.toQ q)=FIp_SemanticValues.decode q := rfl
#print axioms value
end AspisR1.FJn_MainDecode
end
