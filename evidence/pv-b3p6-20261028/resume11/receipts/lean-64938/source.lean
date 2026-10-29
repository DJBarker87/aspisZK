import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- field/mul#0; complete source and owned lexical token sequences. -/
def source_tokens11_field_mul_0 : String := "[\"fn\",\"mul\",\"(\",\"self\",\",\",\"rhs\",\":\",\"QM31\",\")\",\"-\",\">\",\"QM31\",\"{\",\"let\",\"m0\",\"=\",\"prepared_component_mul\",\"(\",\"self\",\".\",\"components\",\"[\",\"0\",\"]\",\",\",\"rhs\",\".\",\"c0\",\")\",\";\",\"let\",\"m1\",\"=\",\"prepared_component_mul\",\"(\",\"self\",\".\",\"components\",\"[\",\"1\",\"]\",\",\",\"rhs\",\".\",\"c1\",\")\",\";\",\"let\",\"m2\",\"=\",\"prepared_component_mul\",\"(\",\"self\",\".\",\"components\",\"[\",\"2\",\"]\",\",\",\"rhs\",\".\",\"c0\",\".\",\"add\",\"(\",\"rhs\",\".\",\"c1\",\")\",\")\",\";\",\"QM31\",\"{\",\"c0\",\":\",\"m0\",\".\",\"add\",\"(\",\"cm31_mul_r\",\"(\",\"m1\",\")\",\")\",\",\",\"c1\",\":\",\"m2\",\".\",\"sub\",\"(\",\"m0\",\")\",\".\",\"sub\",\"(\",\"m1\",\")\",\",\",\"}\",\"}\"]"
def owned_tokens11_field_mul_0 : String := "[\"fn\",\"mul\",\"(\",\"self\",\",\",\"rhs\",\":\",\"QM31\",\")\",\"-\",\">\",\"QM31\",\"{\",\"let\",\"m0\",\"=\",\"prepared_component_mul\",\"(\",\"self\",\".\",\"components\",\"[\",\"0\",\"]\",\",\",\"rhs\",\".\",\"c0\",\")\",\";\",\"let\",\"m1\",\"=\",\"prepared_component_mul\",\"(\",\"self\",\".\",\"components\",\"[\",\"1\",\"]\",\",\",\"rhs\",\".\",\"c1\",\")\",\";\",\"let\",\"m2\",\"=\",\"prepared_component_mul\",\"(\",\"self\",\".\",\"components\",\"[\",\"2\",\"]\",\",\",\"rhs\",\".\",\"c0\",\".\",\"add\",\"(\",\"rhs\",\".\",\"c1\",\")\",\")\",\";\",\"QM31\",\"{\",\"c0\",\":\",\"m0\",\".\",\"add\",\"(\",\"cm31_mul_r\",\"(\",\"m1\",\")\",\")\",\",\",\"c1\",\":\",\"m2\",\".\",\"sub\",\"(\",\"m0\",\")\",\".\",\"sub\",\"(\",\"m1\",\")\",\",\",\"}\",\"}\"]"
theorem body_identity11_field_mul_0 : source_tokens11_field_mul_0 = owned_tokens11_field_mul_0 :=
  token_identity11 source_tokens11_field_mul_0
theorem body_interpretation11_field_mul_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_field_mul_0 = interpret owned_tokens11_field_mul_0 :=
  interpret_identity11 interpret _ _ body_identity11_field_mul_0
#print axioms body_identity11_field_mul_0
#print axioms body_interpretation11_field_mul_0
end PV_B3P_Binding11227
