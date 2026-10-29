import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- field/prepared_component_mul#0; complete source and owned lexical token sequences. -/
def source_tokens11_field_prepared_component_mul_0 : String := "[\"fn\",\"prepared_component_mul\",\"(\",\"left\",\":\",\"[\",\"M31\",\";\",\"3\",\"]\",\",\",\"right\",\":\",\"CM31\",\")\",\"-\",\">\",\"CM31\",\"{\",\"let\",\"m0\",\"=\",\"left\",\"[\",\"0\",\"]\",\".\",\"mul\",\"(\",\"right\",\".\",\"a\",\")\",\";\",\"let\",\"m1\",\"=\",\"left\",\"[\",\"1\",\"]\",\".\",\"mul\",\"(\",\"right\",\".\",\"b\",\")\",\";\",\"let\",\"m2\",\"=\",\"left\",\"[\",\"2\",\"]\",\".\",\"mul\",\"(\",\"right\",\".\",\"a\",\".\",\"add\",\"(\",\"right\",\".\",\"b\",\")\",\")\",\";\",\"CM31\",\"{\",\"a\",\":\",\"m0\",\".\",\"sub\",\"(\",\"m1\",\")\",\",\",\"b\",\":\",\"m2\",\".\",\"sub\",\"(\",\"m0\",\")\",\".\",\"sub\",\"(\",\"m1\",\")\",\",\",\"}\",\"}\"]"
def owned_tokens11_field_prepared_component_mul_0 : String := "[\"fn\",\"prepared_component_mul\",\"(\",\"left\",\":\",\"[\",\"M31\",\";\",\"3\",\"]\",\",\",\"right\",\":\",\"CM31\",\")\",\"-\",\">\",\"CM31\",\"{\",\"let\",\"m0\",\"=\",\"left\",\"[\",\"0\",\"]\",\".\",\"mul\",\"(\",\"right\",\".\",\"a\",\")\",\";\",\"let\",\"m1\",\"=\",\"left\",\"[\",\"1\",\"]\",\".\",\"mul\",\"(\",\"right\",\".\",\"b\",\")\",\";\",\"let\",\"m2\",\"=\",\"left\",\"[\",\"2\",\"]\",\".\",\"mul\",\"(\",\"right\",\".\",\"a\",\".\",\"add\",\"(\",\"right\",\".\",\"b\",\")\",\")\",\";\",\"CM31\",\"{\",\"a\",\":\",\"m0\",\".\",\"sub\",\"(\",\"m1\",\")\",\",\",\"b\",\":\",\"m2\",\".\",\"sub\",\"(\",\"m0\",\")\",\".\",\"sub\",\"(\",\"m1\",\")\",\",\",\"}\",\"}\"]"
theorem body_identity11_field_prepared_component_mul_0 : source_tokens11_field_prepared_component_mul_0 = owned_tokens11_field_prepared_component_mul_0 :=
  token_identity11 source_tokens11_field_prepared_component_mul_0
theorem body_interpretation11_field_prepared_component_mul_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_field_prepared_component_mul_0 = interpret owned_tokens11_field_prepared_component_mul_0 :=
  interpret_identity11 interpret _ _ body_identity11_field_prepared_component_mul_0
#print axioms body_identity11_field_prepared_component_mul_0
#print axioms body_interpretation11_field_prepared_component_mul_0
end PV_B3P_Binding11227
