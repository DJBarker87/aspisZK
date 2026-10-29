import PV_B3P_BodyIdentity11227
namespace PV_B3P_Binding11227
set_option autoImplicit false
/-- field/prepare_component#0; complete source and owned lexical token sequences. -/
def source_tokens11_field_prepare_component_0 : String := "[\"fn\",\"prepare_component\",\"(\",\"component\",\":\",\"CM31\",\")\",\"-\",\">\",\"[\",\"M31\",\";\",\"3\",\"]\",\"{\",\"[\",\"component\",\".\",\"a\",\",\",\"component\",\".\",\"b\",\",\",\"component\",\".\",\"a\",\".\",\"add\",\"(\",\"component\",\".\",\"b\",\")\",\"]\",\"}\"]"
def owned_tokens11_field_prepare_component_0 : String := "[\"fn\",\"prepare_component\",\"(\",\"component\",\":\",\"CM31\",\")\",\"-\",\">\",\"[\",\"M31\",\";\",\"3\",\"]\",\"{\",\"[\",\"component\",\".\",\"a\",\",\",\"component\",\".\",\"b\",\",\",\"component\",\".\",\"a\",\".\",\"add\",\"(\",\"component\",\".\",\"b\",\")\",\"]\",\"}\"]"
theorem body_identity11_field_prepare_component_0 : source_tokens11_field_prepare_component_0 = owned_tokens11_field_prepare_component_0 :=
  token_identity11 source_tokens11_field_prepare_component_0
theorem body_interpretation11_field_prepare_component_0 {α : Sort _} (interpret : String → α) :
    interpret source_tokens11_field_prepare_component_0 = interpret owned_tokens11_field_prepare_component_0 :=
  interpret_identity11 interpret _ _ body_identity11_field_prepare_component_0
#print axioms body_identity11_field_prepare_component_0
#print axioms body_interpretation11_field_prepare_component_0
end PV_B3P_Binding11227
